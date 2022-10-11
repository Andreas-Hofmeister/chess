#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "make-move.rkt")
(require "check.rkt")
(require "legal-moves.rkt")
(require "knight-moves.rkt")

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

(: central-squares (Listof Square-location))
(define central-squares
  (list (Square-location 3 3)
        (Square-location 3 4)
        (Square-location 4 3)
        (Square-location 4 4)))
                      
(: expanded-central-squares (Listof Square-location))
(define expanded-central-squares
  (for*/list : (Listof Square-location)
    ([rank : Integer '(2 3 4 5)]
     [file : Integer '(2 3 4 5)])
    (Square-location rank file)))

(: central-square? (-> Square-location Boolean))
(define (central-square? sq)
  (let ([rank (Square-location-rank sq)]
        [file (Square-location-file sq)])
    (and (>= rank 3) (<= rank 4) (>= file 3) (<= file 4))))

(: expanded-central-square? (-> Square-location Boolean))
(define (expanded-central-square? sq)
  (let ([rank (Square-location-rank sq)]
        [file (Square-location-file sq)])
    (and (>= rank 2) (<= rank 5) (>= file 2) (<= file 5))))

(: expanded-central-squares-without-central-squares (Listof Square-location))
(define expanded-central-squares-without-central-squares
  (filter (lambda ([sq : Square-location]) (not (central-square? sq)))
          expanded-central-squares))

(: expanded-central-square-but-no-central-square? (-> Square-location Boolean))
(define (expanded-central-square-but-no-central-square? sq)
  (and (expanded-central-square? sq)
       (not (central-square? sq))))

(struct Piece-counts ([queens : Integer]
                      [rooks : Integer]
                      [bishops : Integer]
                      [knights : Integer]
                      [pawns : Integer]) #:transparent #:mutable)

(: set-piece-count! (-> Piece-counts Piece Integer Void))
(define (set-piece-count! pc p n)
  (match p
    ['queen (set-Piece-counts-queens! pc n)]
    ['rook (set-Piece-counts-rooks! pc n)]
    ['bishop (set-Piece-counts-bishops! pc n)]
    ['knight (set-Piece-counts-knights! pc n)]
    ['pawn (set-Piece-counts-pawns! pc n)]))

(: get-piece-count (-> Piece-counts Piece Integer))
(define (get-piece-count pc p)
  (match p
    ['queen (Piece-counts-queens pc)]
    ['rook (Piece-counts-rooks pc)]
    ['bishop (Piece-counts-bishops pc)]
    ['knight (Piece-counts-knights pc)]
    ['pawn (Piece-counts-pawns pc)]))

(: add-piece-count! (-> Piece-counts Piece Integer Void))
(define (add-piece-count! pc p n)
  (set-piece-count! pc p (+ (get-piece-count pc p) n)))

(: count-pieces (-> Piece-placements Color (Listof Square-location) Piece-counts))
(define (count-pieces pp c sqs)
  (: result Piece-counts)
  (define result (Piece-counts 0 0 0 0 0))
  (for ([sq : Square-location sqs])
    (match (get-square-by-location pp sq)
      [(Occupied-square sq-c sq-p)
       #:when (and (equal? sq-c c)
                   (not (equal? sq-p 'king)))
       (add-piece-count! result sq-p 1)]
      [_ 'do-nothing]))
  result)

(: count-pieces-in-center (-> Piece-placements Color Piece-counts))
(define (count-pieces-in-center pp c)
  (count-pieces pp c central-squares))

(: count-pieces-in-expanded-center (-> Piece-placements Color Piece-counts))
(define (count-pieces-in-expanded-center pp c)
  (count-pieces pp c expanded-central-squares-without-central-squares))

(: squares-controlled-by-pawn (-> Square-location Color (Listof Square-location)))
(define (squares-controlled-by-pawn loc c)
  (let* ([rank-delta (if (equal? c 'white) 1 -1)]
         [rank (Square-location-rank loc)]
         [file (Square-location-file loc)]
         [new-rank (+ rank rank-delta)])
    (filter location-valid? (list (Square-location new-rank (+ file 1))
                                  (Square-location new-rank (- file 1))))))

(: squares-controlled-by-knight (-> Square-location (Listof Square-location)))
(define (squares-controlled-by-knight loc)
  (knight-target-squares loc))

(: squares-controlled-by-rook (-> Square-location Piece-placements
                                  (Listof Square-location)))
(define (squares-controlled-by-rook loc pp)
  (append (squares-along-direction-until-first-occupied pp loc 1 0)
          (squares-along-direction-until-first-occupied pp loc -1 0)
          (squares-along-direction-until-first-occupied pp loc 0 1)
          (squares-along-direction-until-first-occupied pp loc 0 -1)))

(: squares-controlled-by-bishop (-> Square-location Piece-placements
                                    (Listof Square-location)))
(define (squares-controlled-by-bishop loc pp)
  (append (squares-along-direction-until-first-occupied pp loc 1 1)
          (squares-along-direction-until-first-occupied pp loc 1 -1)
          (squares-along-direction-until-first-occupied pp loc -1 1)
          (squares-along-direction-until-first-occupied pp loc -1 -1)))

(: squares-controlled-by-queen (-> Square-location Piece-placements
                                   (Listof Square-location)))
(define (squares-controlled-by-queen loc pp)
  (append (squares-controlled-by-bishop loc pp)
          (squares-controlled-by-rook loc pp)))

(: squares-controlled-by-king (-> Square-location (Listof Square-location)))
(define (squares-controlled-by-king loc)
  (adjacent-squares loc))

(: squares-controlled-by-piece (-> Piece-placements Color Square-location
                                   (Listof Square-location)))
(define (squares-controlled-by-piece pp c loc)
  (let* ([square (get-square-by-location pp loc)])
    (match square
      ['empty-square '()]
      [(Occupied-square sq-c p)
       #:when (not (equal? sq-c c))
       '()]
      [(Occupied-square _ 'pawn) (squares-controlled-by-pawn loc c)]
      [(Occupied-square _ 'rook) (squares-controlled-by-rook loc pp)]
      [(Occupied-square _ 'knight) (squares-controlled-by-knight loc)]
      [(Occupied-square _ 'bishop) (squares-controlled-by-bishop loc pp)]
      [(Occupied-square _ 'queen) (squares-controlled-by-queen loc pp)]
      [(Occupied-square _ 'king) (squares-controlled-by-king loc)])))

(define-type Control-counts (Vectorof (Vectorof Integer)))

(: make-empty-control-counts (-> (Vectorof (Vectorof Integer))))
(define (make-empty-control-counts)
  (vector (vector 0 0 0 0 0 0 0 0)
          (vector 0 0 0 0 0 0 0 0)
          (vector 0 0 0 0 0 0 0 0)
          (vector 0 0 0 0 0 0 0 0)
          (vector 0 0 0 0 0 0 0 0)
          (vector 0 0 0 0 0 0 0 0)
          (vector 0 0 0 0 0 0 0 0)
          (vector 0 0 0 0 0 0 0 0)))

(: get-control-count (-> Control-counts Integer Integer Integer))
(define (get-control-count ccs rank file)
  (vector-ref (vector-ref ccs file) rank))

(: get-control-count-by-location (-> Control-counts Square-location Integer))
(define (get-control-count-by-location ccs loc)
  (get-control-count ccs (Square-location-rank loc) (Square-location-file loc)))

(: set-control-count! (-> Control-counts Integer Integer Integer Void))
(define (set-control-count! ccs rank file new-count)
  (vector-set! (vector-ref ccs file) rank new-count))

(: add-control-count! (-> Control-counts Integer Integer Integer Void))
(define (add-control-count! ccs rank file delta)
  (set-control-count! ccs rank file (+ delta (get-control-count ccs rank file))))

(: count-control (-> Piece-placements Color Control-counts))
(define (count-control pp c)
  (let ([ccs (make-empty-control-counts)])
    (for* ([rank : Integer rank-indices]
           [file : Integer file-indices])
      (for ([loc : Square-location
                 (squares-controlled-by-piece pp c (Square-location rank file))])
        (add-control-count! ccs
                            (Square-location-rank loc)
                            (Square-location-file loc)
                            1)))
    ccs))

(struct Development ([queens : Integer]
                     [rooks : Integer]
                     [knights : Integer]
                     [bishops : Integer])
  #:transparent #:mutable)

(: queen-development (-> Piece-placements Color Integer))
(define (queen-development pp c)
  (let ([rank (if (equal? c 'white) 0 7)])
    (match (get-square pp rank 3)
      [(Occupied-square sq-c sq-p)
       #:when (and (equal? sq-c c) (equal? sq-p 'queen))
       0]
      [_ 1])))





