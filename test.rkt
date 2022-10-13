#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "legal-moves.rkt")
(require "make-move.rkt")
(require "move-search.rkt")
(require "fen.rkt")


(: pos1 Position)
(define pos1 (pos-from-fen "r1bqk2r/pppp1pp1/2n1pn2/7p/1bBPP3/P1N2P2/1PP3PP/R1BQK1NR b QKqk - 0 1"))

(define pp1 (Position-pp pos1))
(define c1 (count-pieces-in-center pp1 'white))
(define c2 (count-pieces-in-expanded-center pp1 'white))

(define devc (count-development pp1 'black))
