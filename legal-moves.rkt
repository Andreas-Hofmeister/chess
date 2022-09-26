#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "attacks.rkt")
(require "check.rkt")
(require "make-move.rkt")

(provide (all-defined-out))

(: puts-king-in-check? (-> Position Move Boolean))
(define (puts-king-in-check? pos move)
  (in-check? (make-move pos move) (Position-to-move pos)))

(: legal-moves (-> Position (Listof Move)))
(define (legal-moves pos)
  (filter (lambda ([move : Move])
            (not (puts-king-in-check? pos move)))
          (moves-by-player pos (Position-to-move pos))))

(: is-checkmate (-> Position Boolean))
(define (is-checkmate pos)
  (and (in-check? pos (Position-to-move pos))
       (empty? (legal-moves pos))))
