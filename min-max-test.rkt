#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "legal-moves.rkt")
(require "make-move.rkt")
(require "move-search.rkt")
(require "check.rkt")
(require "min-max-evaluation.rkt")
(require "fen.rkt")

(define initial-position (make-initial-position))

(define test1 (pos-from-fen "r7/4k3/2n5/8/8/8/8/R3K3 w - - 0 1"))
(define test2 (pos-from-fen "r7/4k3/8/8/8/2N5/8/R3K3 b - - 0 1"))

(define evs (evaluate-moves evaluate-position
                            legal-moves
                            2
                            test2))

(for-each displayln evs)

(displayln "")

(define ab-evs (evaluate-moves-alpha-beta
                      evaluate-position
                      legal-moves
                      2
                      test2
                      (No-move-evaluation 'minus-infinity)
                      (No-move-evaluation 'plus-infinity)))

(for-each displayln ab-evs)
