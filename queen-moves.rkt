#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "rook-moves.rkt")
(require "bishop-moves.rkt")

(provide (all-defined-out))

(: queen-moves (-> Square-location Color Position (Listof Move)))
(define (queen-moves from-loc c pos)
  (let ([pp (Position-pp pos)])
    (append (rook-moves from-loc c pos) (bishop-moves from-loc c pos))))
