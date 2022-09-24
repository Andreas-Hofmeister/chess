#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(provide (all-defined-out))

(: rook-moves (-> Square-location Color Position (Listof Move)))
(define (rook-moves from-loc c pos)
  (let ([pp (Position-pp pos)])
    (append (moves-along-direction pp c from-loc 1 0)
            (moves-along-direction pp c from-loc -1 0)
            (moves-along-direction pp c from-loc 0 1)
            (moves-along-direction pp c from-loc 0 -1))))
