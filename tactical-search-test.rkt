#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "legal-moves.rkt")
(require "make-move.rkt")
(require "move-search.rkt")
(require "check.rkt")
(require "fen.rkt")

; Daily puzzle 09.12.2022
(define pos1 (pos-from-fen "1r4k1/1r3ppn/4p3/4P1pP/2pP2P1/3Q1P2/P3R3/K1BBq3 w - - 0 1"))
; Daily puzzle 12.12.2022
(define pos1 (pos-from-fen "3rrbk1/ppn3pp/2pn1p2/3p3q/P1PP4/1P1QNN1P/4R1PB/4R1K1 w - - 0 1"))
