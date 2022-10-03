#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "legal-moves.rkt")
(require "make-move.rkt")
(require "move-search.rkt")
(require "fen.rkt")
(require "uci.rkt")

(: pos1 Position)
(define pos1 (pos-from-fen "rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b QKqk e3 0 1"))

(movestring->move

