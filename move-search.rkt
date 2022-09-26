#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "make-move.rkt")
(require "check.rkt")
(require "legal-moves.rkt")

(provide (all-defined-out))

(: value-of-piece (-> Piece Integer))
(define (value-of-piece p)
  (match p
    ['queen 9]
    ['rook 5]
    ['bishop 3]
    ['knight 3]
    ['pawn 1]
    ['king 0]))

(: value-of-square (-> Square Integer))
(define (value-of-square sq)
  (match sq
    ['empty-square 0]
    [(Occupied-square sc p)
     (if (equal? sc 'white)
         (value-of-piece p)
         (- (value-of-piece p)))]))

(: material-balance-of-position (-> Piece-placements Integer))
(define (material-balance-of-position pp)
  (for*/sum : Integer ([rank : Integer rank-indices]
                       [file : Integer file-indices])
    (value-of-square (get-square pp rank file))))

(define-type Position-evaluation (U Normal-evaluation Checkmate 'stalemate))
(struct Normal-evaluation ([value : Integer]))
(struct Checkmate ([color : Color]) #:transparent)

(: position-evaluation<= (-> Position-evaluation Position-evaluation Boolean))
(define (position-evaluation<= ev1 ev2)
  (match* (ev1 ev2)
    [((Normal-evaluation v1) (Normal-evaluation v2)) (<= v1 v2)]
    [((Normal-evaluation v) (Checkmate c))
     (if (equal? c 'white) #t #f)]
    [((Normal-evaluation v) 'stalemate) (<= v 0)]
    [((Checkmate c) _) (if (equal? c 'black) #t #f)]
    [('stalemate (Normal-evaluation v)) (<= 0 v)]
    [('stalemate (Checkmate c)) (if (equal? c 'white) #t #f)]
    [('stalemate 'stalemate) #t]))

; Bigger numbers mean white has a greater advantage
; The result is in "tenth of a pawn" (centipawns)
(: evaluate-position (-> Position Position-evaluation))
(define (evaluate-position pos)
  (let ([number-of-legal-moves (length (legal-moves pos))])
    (if (= 0 number-of-legal-moves)
        (if (in-check? pos (Position-to-move pos))
            (Checkmate (opponent-of (Position-to-move pos)))
            'stalemate)
        (Normal-evaluation (material-balance-of-position (Position-pp pos))))))

(: find-optimal-element (All (A) (-> (Listof A) (-> A A Boolean) A A)))
(define (find-optimal-element l better best-so-far)
  (match l
    ['() best-so-far]
    [(cons a rest)
     (if (better a best-so-far)
         (find-optimal-element rest better a)
         (find-optimal-element rest better best-so-far))]))

(define-type Move-evaluation (U Normal-move-evaluation Checkmate-move-evaluation
                                No-move-evaluation))
(struct Normal-move-evaluation ([move : Move] [v : Integer]) #:transparent)
(struct Checkmate-move-evaluation ([move : Move]
                                   [in-moves : Integer]
                                   [color : Color]) #:transparent)
(struct No-move-evaluation ([v : Position-evaluation]) #:transparent)





