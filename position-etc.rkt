#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "legal-moves.rkt")
(require "make-move.rkt")

(provide (all-defined-out))

; A position together with useful information about it
(struct Position-etc ([position : Position]
                      [legal-moves : (Listof Move)]
                      [white-king-location : Square-location]
                      [white-queens : (Setof Square-location)]
                      [white-rooks : (Setof Square-location)]
                      [white-knights : (Setof Square-location)]
                      [white-bishops : (Setof Square-location)]
                      [white-pawns : (Setof Square-location)]
                      [black-king-location : Square-location]
                      [black-queens : (Setof Square-location)]
                      [black-rooks : (Setof Square-location)]
                      [black-knights : (Setof Square-location)])
  #:transparent)
