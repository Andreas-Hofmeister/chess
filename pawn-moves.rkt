#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(provide (all-defined-out))

(: advance-pawn (-> Color Integer Integer))
(define (advance-pawn c rank-index)
  (match c
    ['white (+ rank-index 1)]
    ['black (- rank-index 1)]))

(: final-rank-of-pawn (-> Color Integer))
(define (final-rank-of-pawn c)
  (match c ['white 7] ['black 0]))

(: starting-rank-of-pawn (-> Color Integer))
(define (starting-rank-of-pawn c)
  (match c ['white 1] ['black 6]))

(: pawn-forward-moves (-> Square-location Color Position (Listof Move)))
(define (pawn-forward-moves pawn-loc c pos)
  (match pos
    [(Position pp _ _ _)
     (match pawn-loc
       [(Square-location rank file)
        (let ([new-rank (advance-pawn c rank)])
          (if (and (indices-valid? new-rank file)
                   (square-empty-rank-file? pp new-rank file)
                   (not (= new-rank (final-rank-of-pawn c))))
              (list (From-to-move pawn-loc (Square-location new-rank file)))
              '()))])]))

(: pawn-captures (-> Square-location Color Position (Listof Move)))
(define (pawn-captures pawn-loc c pos)
  (let* ([rank (Square-location-rank pawn-loc)]
         [file (Square-location-file pawn-loc)]
         [new-rank (advance-pawn c rank)])
    (if (or (= rank (final-rank-of-pawn c))
            (= new-rank (final-rank-of-pawn c)))
        '()
        (let* ([pp (Position-pp pos)]
               [left-capture
                (if (and (<= 1 file)
                         (occupied-by-enemy-piece? pp new-rank (- file 1) c))
                    (list (Capture pawn-loc (Square-location new-rank (- file 1))))
                    '())]
               [right-capture
                (if (and (<= file 6)
                         (occupied-by-enemy-piece? pp new-rank (+ file 1) c))
                    (list (Capture pawn-loc (Square-location new-rank (+ file 1))))
                    '())])
          (append left-capture right-capture)))))

(: pawn-double-steps (-> Square-location Color Position (Listof Move)))
(define (pawn-double-steps pawn-loc c pos)
  (let* ([rank (Square-location-rank pawn-loc)]
         [file (Square-location-file pawn-loc)]
         [pp (Position-pp pos)])
    (if (= (starting-rank-of-pawn c) rank)
        (let* ([step1-rank (advance-pawn c rank)]
               [step2-rank (advance-pawn c step1-rank)])
          (if (and (square-empty-rank-file? pp step1-rank file)
                   (square-empty-rank-file? pp step2-rank file))
              (list (Double-step pawn-loc (Square-location step2-rank file)))
              '()))
        '())))

(: pawn-en-passant-moves (-> Square-location Color Position (Listof Move)))
(define (pawn-en-passant-moves pawn-loc c pos)
  (let* ([rank (Square-location-rank pawn-loc)]
         [file (Square-location-file pawn-loc)]
         [to-rank (advance-pawn c rank)])
    (match pos
      [(Position pp to-move (Some (Pawn-double-step ds-to-rank ds-on-file)) _)
       (if (and (equal? c to-move)
                (= ds-to-rank rank)
                (indices-valid? to-rank ds-on-file)
                (= (difference ds-on-file file) 1))
           (list (En-passant pawn-loc (Square-location to-rank ds-on-file)))
           '())]
      [_ '()])))

(: pawn-forward-promotions (-> Square-location Color Position (Listof Move)))
(define (pawn-forward-promotions pawn-loc c pos)
  (let* ([rank (Square-location-rank pawn-loc)]
         [file (Square-location-file pawn-loc)]
         [pp (Position-pp pos)]
         [new-rank (advance-pawn c rank)])
    (if (and (indices-valid? new-rank file)
             (square-empty-rank-file? pp new-rank file)
             (= new-rank (final-rank-of-pawn c)))
        (for/list: : (Listof Move) ([p : Piece promotion-pieces])
          (Promotion pawn-loc (Square-location new-rank file) p))
        '())))

(: pawn-promotion-captures (-> Square-location Color Position (Listof Move)))
(define (pawn-promotion-captures pawn-loc c pos)
  (let* ([rank (Square-location-rank pawn-loc)]
         [file (Square-location-file pawn-loc)]
         [pp (Position-pp pos)]
         [new-rank (advance-pawn c rank)])
    (if (= new-rank (final-rank-of-pawn c))
        (let ([left-capture
               (if (and (<= 1 file)
                        (occupied-by-enemy-piece? pp new-rank (- file 1) c))
                   (for/list: : (Listof Move)
                     ([p : Piece promotion-pieces])
                     (Promotion-with-capture pawn-loc
                                             (Square-location new-rank (- file 1)) p))
                   '())]
              [right-capture
               (if (and (<= file 6)
                        (occupied-by-enemy-piece? pp new-rank (+ file 1) c))
                   (for/list: : (Listof Move)
                     ([p : Piece promotion-pieces])
                     (Promotion-with-capture pawn-loc
                                             (Square-location new-rank (+ file 1)) p))
                   '())])
          (append left-capture right-capture))
        '())))

(: pawn-moves (-> Square-location Color Position (Listof Move)))
(define (pawn-moves pawn-loc c pos)
  (append (pawn-forward-moves pawn-loc c pos)
          (pawn-captures pawn-loc c pos)
          (pawn-double-steps pawn-loc c pos)
          (pawn-en-passant-moves pawn-loc c pos)
          (pawn-forward-promotions pawn-loc c pos)
          (pawn-promotion-captures pawn-loc c pos)))
