#lang typed/racket
(require racket/match)

(require "basics.rkt")
(provide (all-defined-out))

(define-type Move
  (U From-to-move Capture Double-step En-passant Promotion
     Promotion-with-capture Castle))
(struct From-to-move ([from : Square-location] [to : Square-location]) #:transparent)
(struct Capture ([from : Square-location] [to : Square-location]) #:transparent)
(struct Double-step ([from : Square-location] [to : Square-location]) #:transparent)
(struct En-passant ([from : Square-location] [to : Square-location]) #:transparent)
(struct Promotion ([from : Square-location] [to : Square-location] [piece : Piece])
  #:transparent)
(struct Promotion-with-capture
  ([from : Square-location] [to : Square-location] [piece : Piece])
  #:transparent)
(struct Castle ([color : Color] (castling-type : Castling-type)) #:transparent)

(: promotion-pieces (Listof Piece))
(define promotion-pieces '(rook knight bishop queen))

(: from-of-move (-> Move Square-location))
(define (from-of-move move)
  (match move
    [(From-to-move from _) from]
    [(Capture from _) from]
    [(Double-step from _) from]
    [(En-passant from _) from]
    [(Promotion from _ _) from]
    [(Promotion-with-capture from _ _) from]
    [(Castle 'white _) (Square-location 0 4)]
    [(Castle 'black _) (Square-location 7 4)]))

(: to-of-move (-> Move Square-location))
(define (to-of-move move)
  (match move
    [(From-to-move _ to) to]
    [(Capture _ to) to]
    [(Double-step _ to) to]
    [(En-passant _ to) to]
    [(Promotion _ to _) to]
    [(Promotion-with-capture _ to _) to]
    [(Castle 'white 'queen-side) (Square-location 0 2)]
    [(Castle 'white 'king-side) (Square-location 0 6)]
    [(Castle 'black 'queen-side) (Square-location 7 2)]
    [(Castle 'black 'king-side) (Square-location 7 6)]))

(: is-move-to-empty-square (-> Move Boolean))
(define (is-move-to-empty-square move)
  (match move
    [(From-to-move _ _) #t]
    [(En-passant _ _) #t]
    [(Double-step _ _) #t]
    [(Promotion _ _ _) #t]
    [_ #f]))

(: is-capturing-move (-> Move Boolean))
(define (is-capturing-move move)
  (match move
    [(Capture _ _) #t]
    [(Promotion-with-capture _ _ _) #t]
    [_ #f]))

(struct Movement-vector ([horizontal-step : Integer] [vertical-step : Integer])
  #:transparent)

(: vector-from-a-to-b (-> Square-location Square-location Movement-vector))
(define (vector-from-a-to-b a b)
  (match a
    [(Square-location rank-a file-a)
     (match b
       [(Square-location rank-b file-b)
        (Movement-vector (- file-b file-a) (- rank-b rank-a))])]))

(: movement-vector-length (-> Movement-vector Integer))
(define (movement-vector-length v)
  (+ (abs (Movement-vector-horizontal-step v))
     (abs (Movement-vector-vertical-step v))))

(: add-to-absolute-value (-> Integer Integer Integer))
(define (add-to-absolute-value i to-be-added)
  (let ([sign (if (< i 0) -1 1)])
    (* sign (+ (abs i) to-be-added))))

(: one-step-along-vector
   (-> Square-location Movement-vector (Pairof Square-location Movement-vector)))
(define (one-step-along-vector loc v)
  (match loc
    [(Square-location rank file)
     (match v
       [(Movement-vector 0 0) (cons loc v)]
       [(Movement-vector 0 vstep)
        (cons (Square-location (+ rank vstep) file)
              (Movement-vector 0 (add-to-absolute-value vstep -1)))]
       [(Movement-vector hstep 0)
        (cons (Square-location rank (+ file hstep))
              (Movement-vector (add-to-absolute-value hstep -1) 0))]
       [(Movement-vector hstep vstep)
        (cons (Square-location (+ rank vstep) (+ file hstep))
              (Movement-vector (add-to-absolute-value hstep -1)
                               (add-to-absolute-value vstep -1)))])]))

(: vector-to-adjacent-square? (-> Movement-vector Boolean))
(define (vector-to-adjacent-square? v)
  (match v
    [(Movement-vector hstep vstep)
     (and (<= hstep 1) (<= vstep 1) (< 0 hstep) (< 0 vstep))]))

(: squares-along-vector-empty?
   (-> Piece-placements Square-location Movement-vector Boolean))
(define (squares-along-vector-empty? pp start-loc v)
  (if (= 0 (movement-vector-length v)) #t
      (let* ([one-step (one-step-along-vector start-loc v)]
             [v2 (cdr one-step)]
             [loc2 (car one-step)])
        (if (square-empty? pp start-loc)
            (squares-along-vector-empty? pp loc2 v2)
            #f))))

(: apply-vector (-> Movement-vector Square-location Square-location))
(define (apply-vector v loc)
  (Square-location (+ (Square-location-rank loc)
                      (Movement-vector-vertical-step v))
                   (+ (Square-location-file loc)
                      (Movement-vector-horizontal-step v))))

(: moves-along-direction (-> Piece-placements Color Square-location
                          Integer Integer (Listof Move)))
(define (moves-along-direction pp c from-loc hstep vstep)
  (: loop (-> Square-location (Listof Move) (Listof Move)))
  (define (loop current-loc accumulator)
    (let* ([from-rank (Square-location-rank current-loc)]
           [from-file (Square-location-file current-loc)]
           [next-target-loc
            (Square-location (+ from-rank vstep) (+ from-file hstep))])
    (if (or (not (location-valid? next-target-loc))
            (location-occupied-by-friendly-piece? pp next-target-loc c))
        accumulator
        (if (square-empty? pp next-target-loc)
            (loop next-target-loc
                  (cons (From-to-move from-loc next-target-loc) accumulator))
            (cons (Capture from-loc next-target-loc) accumulator)))))
  (loop from-loc '()))

(: from-to-move-or-capture (-> Piece-placements Color Square-location Square-location Move))
(define (from-to-move-or-capture pp c from-loc to-loc)
  (if (square-empty? pp to-loc)
      (From-to-move from-loc to-loc)
      (Capture from-loc to-loc)))
