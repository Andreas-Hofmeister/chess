#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "make-move.rkt")
(require "check.rkt")
(require "legal-moves.rkt")
(require "knight-moves.rkt")
(require "min-max-evaluation.rkt")

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

; Bigger numbers mean white has a greater advantage
; The result is in "hundreth of a pawn" (centipawns)
(: evaluate-position (-> Position Position-evaluation))
(define (evaluate-position pos)
  (let ([number-of-legal-moves (length (legal-moves pos))])
    (if (= 0 number-of-legal-moves)
        (if (in-check? pos (Position-to-move pos))
            (Checkmate-evaluation (opponent-of (Position-to-move pos)))
            'stalemate)
        (Normal-evaluation (* 100 (material-balance-of-position (Position-pp pos)))))))

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

(: count-piece-at-location (-> Piece-placements Color Piece Integer Integer
                               Integer))
(define (count-piece-at-location pp c p rank file)
  (match (get-square pp rank file)
    [(Occupied-square sq-c sq-p)
     #:when (and (equal? sq-c c) (equal? sq-p p))
     1]
    [_ 0]))

(: queen-development (-> Piece-placements Color Integer))
(define (queen-development pp c)
  (let ([rank (if (equal? c 'white) 0 7)])
    (- 1 (count-piece-at-location pp c 'queen rank 3))))

(: rooks-development (-> Piece-placements Color Integer))
(define (rooks-development pp c)
  (let* ([rank (if (equal? c 'white) 0 7)]
         [a-rook (count-piece-at-location pp c 'rook rank 0)]
         [h-rook (count-piece-at-location pp c 'rook rank 7)])
    (- 2 (+ a-rook h-rook))))

(: knights-development (-> Piece-placements Color Integer))
(define (knights-development pp c)
  (let* ([rank (if (equal? c 'white) 0 7)]
         [b-knight (count-piece-at-location pp c 'knight rank 1)]
         [g-knight (count-piece-at-location pp c 'knight rank 6)])
    (- 2 (+ b-knight g-knight))))

(: bishops-development (-> Piece-placements Color Integer))
(define (bishops-development pp c)
  (let* ([rank (if (equal? c 'white) 0 7)]
         [c-bishop (count-piece-at-location pp c 'bishop rank 2)]
         [f-bishop (count-piece-at-location pp c 'bishop rank 5)])
    (- 2 (+ c-bishop f-bishop))))

(: count-development (-> Piece-placements Color Development))
(define (count-development pp c)
  (Development (queen-development pp c)
               (rooks-development pp c)
               (knights-development pp c)
               (bishops-development pp c)))

(define-type Castling-status (U 'not-castled Castling-info))
(struct Castling-info ([side : Castling-type]
                       [pawn-guards : Integer]
                       [rook-guards : Integer])
  #:transparent #:mutable)

(: count-squares (-> Piece-placements
                     Integer Integer
                     (-> Square (U 'count 'ignore 'abort))
                     (-> Integer Integer Square-location)
                     (-> Integer Integer Boolean)
                     Integer
                     Integer))
(define (count-squares pp rank file cond-f next-f end-f start-v)
  (if (end-f rank file) 0
      (let* ([sq (get-square pp rank file)]
             [next-loc (next-f rank file)]
             [next-rank (Square-location-rank next-loc)]
             [next-file (Square-location-file next-loc)])
        (match (cond-f sq)
          ['count (count-squares pp next-rank next-file cond-f next-f end-f
                                 (+ 1 start-v))]
          ['ignore (count-squares pp next-rank next-file cond-f next-f end-f start-v)]
          ['abort start-v]))))

(: count-rook-guards (-> Piece-placements Color Integer Integer Integer Integer))
(define (count-rook-guards pp c king-rank king-file search-direction)
  (: cond-f (-> Square (U 'count 'ignore 'abort)))
  (define (cond-f sq)
    (match sq
      [(Occupied-square sq-c 'rook)
       #:when (equal? sq-c c)
       'count]
      ['empty-square 'ignore]
      [_ 'abort]))
  (: next-f (-> Integer Integer Square-location))
  (define (next-f rank file)
    (Square-location rank (+ file search-direction)))
  (: end-f (-> Integer Integer Boolean))
  (define (end-f rank file)
    (not (indices-valid? rank file)))
  (let ([first-loc (next-f king-rank king-file)])
    (count-squares pp
                   (Square-location-rank first-loc)
                   (Square-location-file first-loc)
                   cond-f next-f end-f 0)))

(: queen-side-files (Listof Integer))
(define queen-side-files (list 0 1 2))

(: king-side-files (Listof Integer))
(define king-side-files (list 5 6 7))

(: count-pawn-guards (-> Piece-placements Color Castling-type Integer))
(define (count-pawn-guards pp c ct)
  (let ([rank (if (equal? c 'white) 1 6)]
        [files (if (equal? ct 'queen-side) queen-side-files king-side-files)])
    (for/sum ([file : Integer files])
      (match (get-square pp rank file)
        [(Occupied-square sq-c 'pawn)
         #:when
         (equal? sq-c c)
         1]
        [_ 0]))))

(: determine-king-location (-> Integer (U 'queen-side 'king-side 'middle)))
(define (determine-king-location king-file)
    (cond
      [(set-member? queen-side-files king-file) 'queen-side]
      [(set-member? king-side-files king-file) 'king-side]
      [else 'middle]))

(: determine-castling-status (-> Piece-placements Color Castling-status))
(define (determine-castling-status pp c)
  (let* ([king-castling-rank (if (equal? c 'white) 0 7)]
         [pawn-rank (if (equal? c 'white) 1 6)]
         [king-location (car (find-king pp c))]
         [king-rank (Square-location-rank king-location)]
         [king-file (Square-location-file king-location)]
         [king-location (determine-king-location king-file)])
    (cond
      [(not (= king-castling-rank king-rank)) 'not-castled]
      [(equal? king-location 'middle) 'not-castled]
      [else
       (let* ([castling-type
               (if (equal? king-location 'queen-side) 'queen-side 'king-side)]
              [rook-guard-search-direction
               (if (equal? castling-type 'queen-side) 1 -1)]
              [rook-guards
               (count-rook-guards pp c king-rank king-file rook-guard-search-direction)]
              [pawn-guards (count-pawn-guards pp c castling-type)])
         (cond
           [(= rook-guards 0) 'not-castled]
           [(= pawn-guards 0) 'not-castled]
           [else (Castling-info castling-type pawn-guards rook-guards)]))])))

; Having pawns in the center is good.
; Having minor pieces in the center is ok.
; Not having anything in the center is not good.
(: evaluate-central-squares (-> Piece-placements Color Integer))
(define (evaluate-central-squares pp c)
  (let* ([counts (count-pieces-in-center pp c)]
         [pawns (Piece-counts-pawns counts)]
         [bishops (Piece-counts-bishops counts)]
         [knights (Piece-counts-knights counts)])
    (+ (* 4 pawns) bishops knights)))

; Having more control over the central squares is good
(: evaluate-central-control (-> Piece-placements Color Integer))
(define (evaluate-central-control pp c)
  (let ([cc (count-control pp c)])
    (for/sum : Integer ([loc central-squares])
      (get-control-count-by-location cc loc))))

; Developing the pieces is good. Developing the knights and bishops is
; more important than developing the queen and the rooks.
(: evaluate-development (-> Piece-placements Color Integer))
(define (evaluate-development pp c)
  (let* ([dev (count-development pp c)]
         [bishops (Development-bishops dev)]
         [knights (Development-knights dev)]
         [rooks (Development-rooks dev)]
         [queen (Development-queens dev)])
    (+ (* 2 bishops) (* 2 knights) queen rooks)))

; Being castled is better than not being castled. 
(: evaluate-castling (-> Piece-placements Color Integer))
(define (evaluate-castling pp c)
  (match (determine-castling-status pp c)
    ['not-castled 0]
    [_ 1]))

(: balance (-> (-> Color Integer) Integer))
(define (balance f)
  (- (f 'white) (f 'black)))

; Bigger numbers mean white has a greater advantage
; The result is in "hundreth of a pawn" (centipawns)
(: evaluate-opening-position (-> Position Position-evaluation))
(define (evaluate-opening-position pos)
  (let ([number-of-legal-moves (length (legal-moves pos))])
    (if (= 0 number-of-legal-moves)
        (if (in-check? pos (Position-to-move pos))
            (Checkmate-evaluation (opponent-of (Position-to-move pos)))
            'stalemate)
        (let* ([pp (Position-pp pos)]
               [material-balance (material-balance-of-position pp)]
               [center (balance (curry evaluate-central-squares pp))]
               [central-control (balance (curry evaluate-central-control pp))]
               [development (balance (curry evaluate-development pp))]
               [castling (balance (curry evaluate-castling pp))])
        (Normal-evaluation (+ (* 100 material-balance)
                              (* 1 center)
                              (* 1 central-control)
                              (* 1 development)
                              (* 5 castling)))))))

(: checkmate-position-evaluation (-> Position Position-evaluation))
(define (checkmate-position-evaluation pos)
  (let ([number-of-legal-moves (length (legal-moves pos))])
    (if (= 0 number-of-legal-moves)
        (if (in-check? pos (Position-to-move pos))
            (Checkmate-evaluation (opponent-of (Position-to-move pos)))
            'stalemate)
        (Normal-evaluation 0))))

(: capturing-moves (-> (Listof Move) (Listof Move)))
(define (capturing-moves moves)
   (filter capturing-move? moves))

(: puts-opponent-in-check? (-> Position Move Boolean))
(define (puts-opponent-in-check? pos move)
  (in-check? (make-move pos move) (opponent-of (Position-to-move pos))))

(: king-move? (-> Position Move Boolean))
(define (king-move? pos move)
  (match (piece-of-move move (Position-pp pos))
    [(Some p) (eq? p 'king)]
    [_ #f]))

(: move-by-piece-adjacent-to-king? (-> Position Move Boolean))
(define (move-by-piece-adjacent-to-king? pos move)
  (match (get-square-by-location (Position-pp pos) (from-of-move move))
    [(Occupied-square color piece)
     (let* ([needle (Occupied-square color 'king)]
            [adjacent-squares (map (lambda ([loc : Square-location])
                                     (get-square-by-location (Position-pp pos) loc))
                                   (adjacent-squares (from-of-move move)))])
       (exists-in adjacent-squares (lambda ([sq : Square]) (equal? sq needle))))]))

(: move-defends-square? (-> Position Move Square-location Boolean))
(define (move-defends-square? pos move loc)
  (let* ([new-pos (switch-to-move (make-move pos move))]
         [new-moves (legal-moves new-pos)])
    (exists-in new-moves
               (lambda ([move : Move])
                 (equal? loc (to-of-move move))))))

(: blocking-squares-of-pawn-move (-> Move (Listof Square-location)))
(define (blocking-squares-of-pawn-move move)
  (match move
    [(From-to-move _ to) (list to)]
    [(Double-step _ to)
     (let* ([on-file (Square-location-file to)]
            [to-rank (Square-location-rank to)]
            [between-rank (if (= to-rank 3) 2 5)]
            [between-square (Square-location between-rank on-file)])
       (list to between-square))]
    [(Promotion from to _) (list to)]
    [_ '()]))

(: move-blocks-move? (-> Position Move Move Boolean))
(define (move-blocks-move? pos blocking-move move-to-be-blocked)
  (let* ([piece-to-be-blocked (piece-of-move move-to-be-blocked
                                             (Position-pp pos))])
    (match piece-to-be-blocked
      ['knight #f]
      ['pawn (list? (member (to-of-move blocking-move)
                            (blocking-squares-of-pawn-move move-to-be-blocked)))]
      [_ (list? (member (to-of-move blocking-move)
                        (locations-between (from-of-move move-to-be-blocked)
                                           (to-of-move move-to-be-blocked))))])))

(: defensive-moves-for-checkmate-threat (-> Position Move (Listof Move)
                                            (Listof Move)))
(define (defensive-moves-for-checkmate-threat pos threatened-move all-moves)
  (filter (lambda ([move : Move])
            (or (king-move? pos move)
                (move-by-piece-adjacent-to-king? pos move)
                (move-defends-square? pos move (to-of-move threatened-move))
                (move-blocks-move? pos move threatened-move)
                (captures-on-square? move (from-of-move threatened-move))
                (puts-opponent-in-check? pos move)))
          all-moves))


(: flatten-moves (-> (Listof (Listof Move)) (Listof Move)))
(define (flatten-moves lst)
  (apply append lst))

(: checking-moves (-> Position (Listof Move) (Listof Move)))
(define (checking-moves pos moves)
  (filter (curry puts-opponent-in-check? pos) moves))

(: forced-mate-search-moves (-> Position (Listof Move)))
(define (forced-mate-search-moves pos)
  (if (in-check? pos (Position-to-move pos))
      (let ([moves (legal-moves pos)])
        (if (<= (length moves) 2) moves '()))
      (checking-moves pos (legal-moves pos))))

(: forced-mate-search (-> Integer Position (Listof Move-evaluation)))
(define (forced-mate-search depth pos)
  (evaluate-moves checkmate-position-evaluation forced-mate-search-moves depth pos))

(: forced-checkmate-move-evaluation? (-> Move-evaluation Boolean))
(define (forced-checkmate-move-evaluation? ev)
  (match ev
    [(Checkmate-move-evaluation _ _ _) #t]
    [_ #f]))

(: forced-mate-moves (-> (Listof Move-evaluation) (Listof Move-evaluation)))
(define (forced-mate-moves moves)
  (filter forced-checkmate-move-evaluation? moves))

(: threatens-forced-checkmate? (-> Position Move Boolean))
(define (threatens-forced-checkmate? pos move)
  (let ([evs (forced-mate-search 7 (switch-to-move (make-move pos move)))])
    (exists-in evs (lambda ([ev : Move-evaluation])
                     (match ev
                       [(Checkmate-move-evaluation _ _ _) #t]
                       [_ #f])))))

(: forced-checkmate-threats (-> Position (Listof Move) (Listof Move)))
(define (forced-checkmate-threats pos moves)
  (filter (curry threatens-forced-checkmate? pos) moves))

(: tactical-search (-> (-> Position Position-evaluation)
                       (-> Position (Listof Move) (Listof Move))
                       (-> Position (Listof Move) (Listof Move))
                      Integer Position (Listof Move-evaluation)))
(define (tactical-search evaluate-position
                        determine-candidate-offensive-moves
                        determine-candidate-defensive-moves
                        depth pos)
  (let* ([all-moves (legal-moves pos)]
         [offensive-moves (determine-candidate-offensive-moves pos all-moves)]
         [defensive-moves (determine-candidate-defensive-moves pos all-moves)]
         [do-nothing (No-move-evaluation (evaluate-position pos))])
    (cond
      [(= depth 0) (list do-nothing)]
      [(> depth 0)
       (let* ([player (Position-to-move pos)]
              [opponent (opponent-of player)]
              [min-or-max-opponent (evaluation-function-for-player opponent)]
              [min-or-max-self (evaluation-function-for-player player)]
              [better? (if (equal? player 'white) move-evaluation> move-evaluation<=)]
              [evaluate-move
               (lambda ([move : Move])
                 (discounted-evaluation
                  move
                  (min-or-max-opponent
                   (tactical-search evaluate-position
                                    determine-candidate-offensive-moves
                                    determine-candidate-defensive-moves
                                    (- depth 1)
                                    (make-move pos move)))))]
              [offensive-evaluations (map evaluate-move offensive-moves)]
              [defensive-evaluations (map evaluate-move defensive-moves)]
              [optimal-offense (min-or-max-self offensive-evaluations)]
              [optimal-defense (min-or-max-self defensive-evaluations)])
         (if (better? do-nothing optimal-offense)
             defensive-evaluations
             (append offensive-evaluations defensive-evaluations)))]
         [else '()])))

(: offensive-moves (-> Position (Listof Move) (Listof Move)))
(define (offensive-moves pos moves)
  (filter (lambda ([move : Move])
            (or (capturing-move? move)
                (puts-opponent-in-check? pos move)
                (threatens-forced-checkmate? pos move)))
          moves))

(: defensive-moves (-> Position (Listof Move) (Listof Move)))
(define (defensive-moves pos moves)
  (if (in-check? pos (Position-to-move pos))
      moves
      '()))

(: move-evaluation-eq? (-> Move Move-evaluation Boolean))
(define (move-evaluation-eq? move ev)
  (match ev
    [(Normal-move-evaluation ev-move _)
     (equal? ev-move move)]
    [(Checkmate-move-evaluation ev-move _ _)
     (equal? ev-move move)]
    [_ #f]))

(: cmp-of-player (-> Color (-> Move-evaluation Move-evaluation Boolean)))
(define (cmp-of-player c)
  (match c
    ['black move-evaluation<=]
    ['white
     (lambda ([ev1 : Move-evaluation] [ev2 : Move-evaluation])
       (move-evaluation<= ev2 ev1))]))

(: position-evaluation->integer (-> Position-evaluation Integer))
(define (position-evaluation->integer pev)
  (match pev
    [(Normal-evaluation v) v]
    [(Checkmate-evaluation c)
     (match c
       ['black -10000]
       ['white 10000])]
    ['stalemate 0]))

(: move-evaluation->integer (-> Move-evaluation Integer))
(define (move-evaluation->integer mev)
  (match mev
    [(Normal-move-evaluation _ v) v]
    [(Checkmate-move-evaluation move n-moves c)
     (match c
       ['black (+ -10000 n-moves)]
       ['white (- 10000 n-moves)])]
    [(No-move-evaluation pev) (position-evaluation->integer pev)]))

(: moves-of-evaluations (-> (Listof Move-evaluation) (Listof Move)))
(define (moves-of-evaluations evs)
  (match evs
    ['() '()]
    [(cons ev tl)
     (match ev
       [(Normal-move-evaluation m _) (cons m (moves-of-evaluations tl))]
       [(Checkmate-move-evaluation m _ _) (cons m (moves-of-evaluations tl))]
       [_ (moves-of-evaluations tl)])]))

(: best-among-all-moves (-> Position Integer
                            (-> Position Position-evaluation)
                            (Listof Move)))
(define (best-among-all-moves pos depth ev-f)
  (let* ([evaluations (evaluate-moves ev-f legal-moves depth pos)]
         [cmp (cmp-of-player (Position-to-move pos))]
         [sorted-evaluations (sort evaluations cmp)]
         [best-value (move-evaluation->integer (car sorted-evaluations))]
         [best-evaluations
          (filter (lambda ([ev : Move-evaluation])
                    (= (move-evaluation->integer ev) best-value))
                  sorted-evaluations)])
    (moves-of-evaluations best-evaluations)))

(: sort-evaluations (-> (Listof Move-evaluation)
                        Color
                        (Listof Move-evaluation)))
(define (sort-evaluations evs to-move)
  (let* ([cmp (cmp-of-player to-move)]
         [sorted-evaluations (sort evs cmp)])
    sorted-evaluations))

(: best-evaluations (-> (Listof Move-evaluation)
                        Color
                        (Listof Move-evaluation)))
(define (best-evaluations evs to-move)
  (let* ([sorted-evaluations (sort-evaluations evs to-move)]
         [best-value (if (empty? evs) 0
                         (move-evaluation->integer (car sorted-evaluations)))])
    (filter (lambda ([ev : Move-evaluation])
              (= (move-evaluation->integer ev) best-value))
            sorted-evaluations)))

(struct Attack ([attacker-location : Square-location]
                [attacker-piece : Piece]
                [attacker-color : Color]
                [target-location : Square-location]
                [target-piece : Piece]
                [target-color : Color]
                [directness : Integer])
  #:transparent)

(: attacks-in-direction (-> Piece-placements
                            Square-location
                            Square-location
                            Integer
                            Color
                            Piece
                            Integer Integer
                            (HashTable Piece Integer)
                            Integer
                            (Listof Attack)))
(define (attacks-in-direction pp attacker-loc current-loc current-directness color piece dir-x dir-y extension-pieces fuel)
  (if (or (not (location-valid? current-loc)) (= 0 fuel)) '()
      (match (get-square-by-location pp current-loc)
        ['empty-square (attacks-in-direction pp attacker-loc
                                             (add-to-square-location current-loc dir-x dir-y)
                                             current-directness
                                             color piece dir-x dir-y extension-pieces (- fuel 1))]
        [(Occupied-square target-color target-piece)
         (let* ([new-attack (Attack attacker-loc piece color current-loc target-piece target-color current-directness)]
                [new-attacks (if (eq? color target-color) '() (list new-attack))])
           (if (hash-has-key? extension-pieces target-piece)
               (append new-attacks
                       (attacks-in-direction pp attacker-loc
                                             (add-to-square-location current-loc dir-x dir-y)
                                             (+ current-directness 1)
                                             color piece dir-x dir-y extension-pieces (min (- fuel 1)
                                                                                           (hash-ref extension-pieces target-piece))))
               new-attacks))])))

(: attacks-in-directions (-> Piece-placements
                            Square-location
                            Color
                            Piece
                            (Listof (Pairof Integer Integer))
                            (HashTable Piece Integer)
                            (Listof Attack)))
(define (attacks-in-directions pp attacker-loc color piece dir-list extension-pieces)
  (if (empty? dir-list) '()
      (let* ([dir (car dir-list)]
             [delta-x (car dir)]
             [delta-y (cdr dir)])
        (append (attacks-in-direction pp attacker-loc (add-to-square-location attacker-loc delta-x delta-y)
                                      0 color piece delta-x delta-y extension-pieces 8)
                (attacks-in-directions pp attacker-loc color piece (cdr dir-list) extension-pieces)))))

(define up-down-left-right-dirs (list (cons 1 0) (cons -1 0) (cons 0 1) (cons 0 -1)))
(define diagonal-up-dirs (list (cons 1 1) (cons -1 1)))
(define diagonal-down-dirs (list (cons 1 -1) (cons -1 -1)))
(define up-down-left-right-extensions (hash 'queen 8 'rook 8))
(: diagonal-up-extensions (-> Color (HashTable Piece Integer)))
(define (diagonal-up-extensions color)
  (if (eq? color 'white) (hash 'queen 8 'bishop 8 'pawn 1)
      (hash 'queen 8 'bishop 8)))
(: diagonal-down-extensions (-> Color (HashTable Piece Integer)))
(define (diagonal-down-extensions color)
  (if (eq? color 'white) (hash 'queen 8 'bishop 8)
      (hash 'queen 8 'bishop 8 'pawn 1)))
(define knight-jump-deltas (list (cons 1 2) (cons -1 2) (cons -2 1) (cons -2 -1)
                                 (cons -1 -2) (cons 1 -2) (cons 2 -1) (cons 2 1)))
(: pawn-deltas (-> Color (Listof (Pairof Integer Integer))))
(define (pawn-deltas color)
  (let ([delta-y (if (eq? color 'white) 1 -1)])
    (list (cons 1 delta-y) (cons -1 delta-y))))
(define king-deltas (list (cons 1 0) (cons 1 1) (cons 0 1) (cons -1 1)
                          (cons -1 0) (cons -1 -1) (cons 0 -1) (cons 1 -1)))
    
(: attacks-by-queen (-> Piece-placements Square-location Color
                        (Listof Attack)))
(define (attacks-by-queen pp loc color)
  (append (attacks-in-directions pp loc color 'queen up-down-left-right-dirs up-down-left-right-extensions)
          (attacks-in-directions pp loc color 'queen diagonal-up-dirs (diagonal-up-extensions color))
          (attacks-in-directions pp loc color 'queen diagonal-down-dirs (diagonal-down-extensions color))))

(: attacks-by-rook (-> Piece-placements Square-location Color
                       (Listof Attack)))
(define (attacks-by-rook pp loc color)
  (attacks-in-directions pp loc color 'rook up-down-left-right-dirs up-down-left-right-extensions))

(: attacks-by-bishop (-> Piece-placements Square-location Color
                         (Listof Attack)))
(define (attacks-by-bishop pp loc color)
  (append (attacks-in-directions pp loc color 'bishop diagonal-up-dirs (diagonal-up-extensions color))
          (attacks-in-directions pp loc color 'bishop diagonal-down-dirs (diagonal-down-extensions color))))

(: one-step-attack (-> Piece-placements Square-location Piece Color Integer Integer
                       (Listof Attack)))
(define (one-step-attack pp loc piece color delta-x delta-y)
  (let ([target-loc (add-to-square-location loc delta-x delta-y)])
    (if (location-valid? target-loc)
        (match (get-square-by-location pp target-loc)
          [(Occupied-square target-color target-piece)
           #:when (not (eq? target-color color))
           (list (Attack loc piece color target-loc target-piece target-color 0))]
          [_ '()])
        '())))

(: one-step-attacks (-> Piece-placements Square-location Piece Color
                        (Listof (Pairof Integer Integer))
                        (Listof Attack)))
(define (one-step-attacks pp loc piece color deltas)
  (: iter (-> (Listof (Pairof Integer Integer)) (Listof Attack)))
  (define (iter deltas)
    (if (empty? deltas) '()
        (append (one-step-attack pp loc piece color (car (car deltas)) (cdr (car deltas)))
                (iter (cdr deltas)))))
  (iter deltas))

(: attacks-by-knight (-> Piece-placements Square-location Color
                         (Listof Attack)))
(define (attacks-by-knight pp loc color)
  (one-step-attacks pp loc 'knight color knight-jump-deltas))

(: attacks-by-pawn (-> Piece-placements Square-location Color
                       (Listof Attack)))
(define (attacks-by-pawn pp loc color)
  (one-step-attacks pp loc 'pawn color (pawn-deltas color)))

(: attacks-by-king (-> Piece-placements Square-location Color
                       (Listof Attack)))
(define (attacks-by-king pp loc color)
  (one-step-attacks pp loc 'king color king-deltas))

(: attacks-of-piece (-> Piece-placements Square-location Piece Color
                        (Listof Attack)))
(define (attacks-of-piece pp loc piece color)
  (match piece
    ['pawn (attacks-by-pawn pp loc color)]
    ['rook (attacks-by-rook pp loc color)]
    ['bishop (attacks-by-bishop pp loc color)]
    ['knight (attacks-by-knight pp loc color)]
    ['queen (attacks-by-queen pp loc color)]
    ['king (attacks-by-king pp loc color)]))

(struct Attacks ([white : (Listof Attack)]
                 [black : (Listof Attack)])
  #:transparent)

(: attacks-of-pp (-> Piece-placements Attacks))
(define (attacks-of-pp pp)
  (let ([white-attacks : (Listof Attack) '()]
        [black-attacks : (Listof Attack) '()])
    (for ([loc valid-locations])
      (match (get-square-by-location pp loc)
        [(Occupied-square color piece)
         #:when (eq? color 'white)
         (set! white-attacks (append white-attacks (attacks-of-piece pp loc piece color)))]
        [(Occupied-square color piece)
         (set! black-attacks (append black-attacks (attacks-of-piece pp loc piece color)))]
        [_ '()]))
    (Attacks white-attacks black-attacks)))

(: attack->string (-> Attack String))
(define (attack->string attack)
  (match attack
    [(Attack a-loc a-piece a-color t-loc t-piece t-color directness)
     (format "~a ~a on ~a attacks ~a ~a on ~a (directness: ~a)"
             a-color a-piece (square-location->string a-loc)
             t-color t-piece (square-location->string t-loc) directness)]))

(: attack-list->string (-> (Listof Attack) String))
(define (attack-list->string attacks)
  (foldr (lambda ([attack : Attack] [s : String])
           (string-append (attack->string attack) "\n" s))
         ""
         attacks))

(: attacks->string (-> Attacks String))
(define (attacks->string attacks)
  (string-append "white attacks:\n" (attack-list->string (Attacks-white attacks))
                 "\nblack attacks:\n" (attack-list->string (Attacks-black attacks))))

(struct Defense ([defender-location : Square-location]
                 [defender-piece : Piece]
                 [color : Color]
                 [target-location : Square-location]
                 [target-piece : Piece]
                 [directness : Integer])
  #:transparent)

(: defenses-in-direction (-> Piece-placements
                             Square-location
                             Square-location
                             Integer
                             Color
                             Piece
                             Integer Integer
                             (HashTable Piece Integer)
                             Integer
                             (Listof Defense)))
(define (defenses-in-direction pp defender-loc current-loc current-directness color piece dir-x dir-y extension-pieces fuel)
  (if (or (not (location-valid? current-loc)) (= 0 fuel)) '()
      (match (get-square-by-location pp current-loc)
        ['empty-square (defenses-in-direction pp defender-loc
                         (add-to-square-location current-loc dir-x dir-y)
                         current-directness
                         color piece dir-x dir-y extension-pieces (- fuel 1))]
        [(Occupied-square target-color target-piece)
         #:when (eq? target-color color)
         (let ([defense (Defense defender-loc piece color current-loc target-piece current-directness)])
           (if (hash-has-key? extension-pieces target-piece)
               (cons defense
                     (defenses-in-direction pp defender-loc
                       (add-to-square-location current-loc dir-x dir-y)
                       (+ current-directness 1)
                       color piece dir-x dir-y extension-pieces (min (- fuel 1)
                                                                     (hash-ref extension-pieces target-piece))))
               (list defense)))]
        [_ '()])))

(: defenses-in-directions (-> Piece-placements
                              Square-location
                              Color
                              Piece
                              (Listof (Pairof Integer Integer))
                              (HashTable Piece Integer)
                              (Listof Defense)))
(define (defenses-in-directions pp defender-loc color piece dir-list extension-pieces)
  (if (empty? dir-list) '()
      (let* ([dir (car dir-list)]
             [delta-x (car dir)]
             [delta-y (cdr dir)])
        (append (defenses-in-direction pp defender-loc (add-to-square-location defender-loc delta-x delta-y)
                  0 color piece delta-x delta-y extension-pieces 8)
                (defenses-in-directions pp defender-loc color piece (cdr dir-list) extension-pieces)))))

(: defenses-by-queen (-> Piece-placements Square-location Color
                         (Listof Defense)))
(define (defenses-by-queen pp loc color)
  (append (defenses-in-directions pp loc color 'queen up-down-left-right-dirs up-down-left-right-extensions)
          (defenses-in-directions pp loc color 'queen diagonal-up-dirs (diagonal-up-extensions color))
          (defenses-in-directions pp loc color 'queen diagonal-down-dirs (diagonal-down-extensions color))))

(: defenses-by-rook (-> Piece-placements Square-location Color
                        (Listof Defense)))
(define (defenses-by-rook pp loc color)
  (defenses-in-directions pp loc color 'rook up-down-left-right-dirs up-down-left-right-extensions))

(: defenses-by-bishop (-> Piece-placements Square-location Color
                          (Listof Defense)))
(define (defenses-by-bishop pp loc color)
  (append (defenses-in-directions pp loc color 'bishop diagonal-up-dirs (diagonal-up-extensions color))
          (defenses-in-directions pp loc color 'bishop diagonal-down-dirs (diagonal-down-extensions color))))

(: one-step-defense (-> Piece-placements Square-location Piece Color Integer Integer
                        (Listof Defense)))
(define (one-step-defense pp loc piece color delta-x delta-y)
  (let ([target-loc (add-to-square-location loc delta-x delta-y)])
    (if (location-valid? target-loc)
        (match (get-square-by-location pp target-loc)
          [(Occupied-square target-color target-piece)
           #:when (eq? target-color color)
           (list (Defense loc piece color target-loc target-piece 0))]
          [_ '()])
        '())))

(: one-step-defenses (-> Piece-placements Square-location Piece Color
                         (Listof (Pairof Integer Integer))
                         (Listof Defense)))
(define (one-step-defenses pp loc piece color deltas)
  (: iter (-> (Listof (Pairof Integer Integer)) (Listof Defense)))
  (define (iter deltas)
    (if (empty? deltas) '()
        (append (one-step-defense pp loc piece color (car (car deltas)) (cdr (car deltas)))
                (iter (cdr deltas)))))
  (iter deltas))

(: defenses-by-knight (-> Piece-placements Square-location Color
                          (Listof Defense)))
(define (defenses-by-knight pp loc color)
  (one-step-defenses pp loc 'knight color knight-jump-deltas))

(: defenses-by-pawn (-> Piece-placements Square-location Color
                        (Listof Defense)))
(define (defenses-by-pawn pp loc color)
  (one-step-defenses pp loc 'pawn color (pawn-deltas color)))

(: defenses-by-king (-> Piece-placements Square-location Color
                        (Listof Defense)))
(define (defenses-by-king pp loc color)
  (one-step-defenses pp loc 'king color king-deltas))

(: defenses-of-piece (-> Piece-placements Square-location Piece Color
                         (Listof Defense)))
(define (defenses-of-piece pp loc piece color)
  (match piece
    ['pawn (defenses-by-pawn pp loc color)]
    ['rook (defenses-by-rook pp loc color)]
    ['bishop (defenses-by-bishop pp loc color)]
    ['knight (defenses-by-knight pp loc color)]
    ['queen (defenses-by-queen pp loc color)]
    ['king (defenses-by-king pp loc color)]))

(struct Defenses ([white : (Listof Defense)]
                  [black : (Listof Defense)])
  #:transparent)

(: defenses-of-pp (-> Piece-placements Defenses))
(define (defenses-of-pp pp)
  (let ([white-defenses : (Listof Defense) '()]
        [black-defenses : (Listof Defense) '()])
    (for ([loc valid-locations])
      (match (get-square-by-location pp loc)
        [(Occupied-square color piece)
         #:when (eq? color 'white)
         (set! white-defenses (append white-defenses (defenses-of-piece pp loc piece color)))]
        [(Occupied-square color piece)
         (set! black-defenses (append black-defenses (defenses-of-piece pp loc piece color)))]
        [_ '()]))
    (Defenses white-defenses black-defenses)))

(: defense->string (-> Defense String))
(define (defense->string attack)
  (match attack
    [(Defense d-loc d-piece color t-loc t-piece directness)
     (format "~a ~a on ~a defends ~a ~a on ~a (directness: ~a)"
             color d-piece (square-location->string d-loc)
             color t-piece (square-location->string t-loc) directness)]))

(: defense-list->string (-> (Listof Defense) String))
(define (defense-list->string defenses)
  (foldr (lambda ([defense : Defense] [s : String])
           (string-append (defense->string defense) "\n" s))
         ""
         defenses))

(: defenses->string (-> Defenses String))
(define (defenses->string defenses)
  (string-append "white defenses:\n" (defense-list->string (Defenses-white defenses))
                 "\nblack defenses:\n" (defense-list->string (Defenses-black defenses))))

(: sort-attacks-by-target (-> (Listof Attack) 
                              (HashTable Square-location (Listof Attack))))
(define (sort-attacks-by-target attacks)
  (: sorted-attacks (HashTable Square-location (Listof Attack)))
  (define sorted-attacks (make-hash))
  (: iter (-> (Listof Attack) (HashTable Square-location (Listof Attack))))
  (define (iter remaining-attacks)
    (if (empty? remaining-attacks) sorted-attacks
        (let* ([attack (car remaining-attacks)]
               [target-loc (Attack-target-location attack)]
               [attacks-so-far : (Listof Attack) (hash-ref! sorted-attacks target-loc (lambda () '()))])
          (hash-set! sorted-attacks target-loc (cons attack attacks-so-far))
          (iter (cdr remaining-attacks)))))
  (iter attacks))

(: sort-defenses-by-target (-> (Listof Defense) 
                               (HashTable Square-location (Listof Defense))))
(define (sort-defenses-by-target defenses)
  (: sorted-defenses (HashTable Square-location (Listof Defense)))
  (define sorted-defenses (make-hash))
  (: iter (-> (Listof Defense) (HashTable Square-location (Listof Defense))))
  (define (iter remaining-defenses)
    (if (empty? remaining-defenses) sorted-defenses
        (let* ([defense (car remaining-defenses)]
               [target-loc (Defense-target-location defense)]
               [defenses-so-far : (Listof Defense) (hash-ref! sorted-defenses target-loc (lambda () '()))])
          (hash-set! sorted-defenses target-loc (cons defense defenses-so-far))
          (iter (cdr remaining-defenses)))))
  (iter defenses))

(: sort-defenses-by-defender (-> (Listof Defense) 
                                 (HashTable Square-location (Listof Defense))))
(define (sort-defenses-by-defender defenses)
  (: sorted-defenses (HashTable Square-location (Listof Defense)))
  (define sorted-defenses (make-hash))
  (: iter (-> (Listof Defense) (HashTable Square-location (Listof Defense))))
  (define (iter remaining-defenses)
    (if (empty? remaining-defenses) sorted-defenses
        (let* ([defense (car remaining-defenses)]
               [defender-loc (Defense-defender-location defense)]
               [defenses-so-far : (Listof Defense) (hash-ref! sorted-defenses defender-loc (lambda () '()))])
          (hash-set! sorted-defenses defender-loc (cons defense defenses-so-far))
          (iter (cdr remaining-defenses)))))
  (iter defenses))

(: sorted-attacks->string (-> (HashTable Square-location (Listof Attack)) String))
(define (sorted-attacks->string sorted-attacks)
  (let* ([result ""])
    (hash-for-each sorted-attacks
                   (lambda ([target-location : Square-location]
                            [attacks : (Listof Attack)])
                     (let ([target-color (Attack-target-color (car attacks))]
                           [target-piece (Attack-target-piece (car attacks))])
                       (set! result (format "~a~a ~a on ~a is attacked by:\n"
                                            (if (non-empty-string? result) (format "~a\n" result) result)
                                            target-color target-piece
                                            (square-location->string target-location)))
                       (set! result (string-append result (attack-list->string attacks))))))
    result))

(: sorted-defenses->string (-> (HashTable Square-location (Listof Defense)) String))
(define (sorted-defenses->string sorted-defenses)
  (let* ([result ""])
    (hash-for-each sorted-defenses
                   (lambda ([target-location : Square-location]
                            [defenses : (Listof Defense)])
                     (let ([target-color (Defense-color (car defenses))]
                           [target-piece (Defense-target-piece (car defenses))])
                       (set! result (format "~a~a ~a on ~a is defended by:\n"
                                            (if (non-empty-string? result) (format "~a\n" result) result)
                                            target-color target-piece
                                            (square-location->string target-location)))
                       (set! result (string-append result (defense-list->string defenses))))))
    result))

(: value-of-piece-for-en-prise (-> Piece Integer))
(define (value-of-piece-for-en-prise p)
  (match p
    ['queen 9]
    ['rook 5]
    ['bishop 3]
    ['knight 3]
    ['pawn 1]
    ['king 700]))

(: piece< (-> Piece Piece Boolean))
(define (piece< piece1 piece2)
  (< (value-of-piece-for-en-prise piece1) (value-of-piece-for-en-prise piece2)))

(: sort-attacks-by-piece-value (-> (Listof Attack) (Listof Attack)))
(define (sort-attacks-by-piece-value attacks)
  (sort attacks
        (lambda ([attack1 : Attack] [attack2 : Attack])
          (piece< (Attack-attacker-piece attack1)
                  (Attack-attacker-piece attack2)))))

(: sort-defenses-by-piece-value (-> (Listof Defense) (Listof Defense)))
(define (sort-defenses-by-piece-value defenses)
  (sort defenses
        (lambda ([defense1 : Defense] [defense2 : Defense])
          (piece< (Defense-defender-piece defense1)
                  (Defense-defender-piece defense2)))))


    
