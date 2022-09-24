#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(provide (all-defined-out))

(: bishop-moves (-> Square-location Color Position (Listof Move)))
(define (bishop-moves from-loc c pos)
  (let ([pp (Position-pp pos)])
    (append (moves-along-direction pp c from-loc 1 1)
            (moves-along-direction pp c from-loc 1 -1)
            (moves-along-direction pp c from-loc -1 1)
            (moves-along-direction pp c from-loc -1 -1))))
