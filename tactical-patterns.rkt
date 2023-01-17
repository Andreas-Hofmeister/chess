#lang racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "legal-moves.rkt")
(require "make-move.rkt")
(require "move-search.rkt")
(require "check.rkt")
(require "fen.rkt")

; The player with color 'color' has checkmated his opponent
(struct Checkmate ([color : Color]) #:transparent)

; Using a sequence of checks, the player with color 'color' can force a checkmate in
; 'number-of-moves' moves, with the first move being 'first-move'
(struct Forced-checkmate ([color : Color]
                          [number-of-moves : Integer]
                          [first-move : 