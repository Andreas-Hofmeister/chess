#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "make-move.rkt")
(require "check.rkt")
(require "legal-moves.rkt")

(provide (all-defined-out))

(: maximal-value Integer)
(define maximal-value 9999)

(: minimal-value Integer)
(define minimal-value -9999)

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

(: move-evaluation<= (-> Move-evaluation Move-evaluation Boolean))
(define (move-evaluation<= ev1 ev2)
  (match* (ev1 ev2)
    [((Normal-move-evaluation _ v1) (Normal-move-evaluation _ v2))
     (<= v1 v2)]
    [((Normal-move-evaluation _ v) (Checkmate-move-evaluation _ in-moves c))
     (if (equal? c 'white) #t #f)]
    [((Normal-move-evaluation _ v) (No-move-evaluation pv))
     (position-evaluation<= (Normal-evaluation v) pv)]
    [((Checkmate-move-evaluation _ _ c) (Normal-move-evaluation _ v))
     (if (equal? c 'black) #t #f)]
    [((Checkmate-move-evaluation _ n1 c1) (Checkmate-move-evaluation _ n2 c2))
     (match* (c1 c2)
       [('white 'white) (<= n2 n1)]
       [('white 'black) #f]
       [('black 'white) #t]
       [('black 'black) (<= n1 n2)])]
    [((Checkmate-move-evaluation _ _ c) (No-move-evaluation v))
     (position-evaluation<= (Checkmate c) v)]
    [((No-move-evaluation pv) (Normal-move-evaluation _ v))
     (position-evaluation<= pv (Normal-evaluation v))]
    [((No-move-evaluation v) (Checkmate-move-evaluation _ _ c))
     (position-evaluation<= v (Checkmate c))]
    [((No-move-evaluation v1) (No-move-evaluation v2))
     (position-evaluation<= v1 v2)]))

(: move-evaluation> (-> Move-evaluation Move-evaluation Boolean))
(define (move-evaluation> ev1 ev2)
  (not (move-evaluation<= ev1 ev2)))

(: value-of-normal-evaluation (-> Move-evaluation Integer))
(define (value-of-normal-evaluation ev)
  (match ev
    [(Normal-move-evaluation _ v) v]
    [_ 0]))

(: discounted-evaluation (-> Move Move-evaluation Move-evaluation))
(define (discounted-evaluation move ev)
  (match ev
    [(Normal-move-evaluation _ v) (Normal-move-evaluation move v)]
    [(Checkmate-move-evaluation _ in-moves c)
     (Checkmate-move-evaluation move (+ in-moves 1) c)]
    [(No-move-evaluation pv)
     (match pv
       [(Normal-evaluation v) (Normal-move-evaluation move v)]
       [(Checkmate c) (Checkmate-move-evaluation move 1 c)]
       ['stalemate (Normal-move-evaluation move 0)])]))

(: moves-worth-considering (-> Position (Listof Move)))
(define (moves-worth-considering pos)
  (legal-moves pos))

(: minimal-evaluation (-> (Listof Move-evaluation) Move-evaluation))
(define (minimal-evaluation l)
  (match l
    ['() (No-move-evaluation (Normal-evaluation maximal-value))]
    [(cons h tl) (find-optimal-element tl move-evaluation<= h)]))

(: maximal-evaluation (-> (Listof Move-evaluation) Move-evaluation))
(define (maximal-evaluation l)
  (match l
    ['() (No-move-evaluation (Normal-evaluation minimal-value))]
    [(cons h tl) (find-optimal-element tl move-evaluation> h)]))

(: evaluation-function-for-player
   (-> Color (-> (Listof Move-evaluation) Move-evaluation)))
(define (evaluation-function-for-player c)
  (match c
    ['white maximal-evaluation]
    ['black minimal-evaluation]))

(: evaluate-moves (-> Integer Position (Listof Move-evaluation)))
(define (evaluate-moves depth pos)
  (let ([moves-to-consider (moves-worth-considering pos)])
    (if (empty? moves-to-consider)
        (list (No-move-evaluation (evaluate-position pos)))
        (cond
          [(= depth 0) (list (No-move-evaluation (evaluate-position pos)))]
          [(> depth 0)
           (let* ([player (Position-to-move pos)]
                  [opponent (opponent-of player)]
                  [min-or-max (evaluation-function-for-player opponent)]
                  [evaluate-move
                   (lambda ([move : Move])
                     (discounted-evaluation
                      move
                      (min-or-max
                       (evaluate-moves (- depth 1) (make-move pos move)))))])
             (map evaluate-move moves-to-consider))]
          [else '()]))))


