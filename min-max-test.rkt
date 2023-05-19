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

(define evs (sort (evaluate-moves evaluate-opening-position
                            legal-moves
                            2
                            initial-position)
                  move-evaluation<=))

(for-each displayln evs)

(displayln "")

(define ab-evs (sort (evaluate-moves-alpha-beta
                      evaluate-opening-position
                      legal-moves
                      2
                      initial-position
                      (No-move-evaluation 'minus-infinity)
                      (No-move-evaluation 'plus-infinity))
                     move-evaluation<=))

(for-each displayln ab-evs)