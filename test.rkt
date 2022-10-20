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
(define pos2 (pos-from-fen "rnbqkbnr/pppppppp/8/8/2B2BN1/3Q4/PPPPPPPP/1N1R1RK1 w kq - 0 1"))
(define rgc (count-rook-guards (Position-pp pos2) 'white 0 6 -1))
(define pgc (count-pawn-guards (Position-pp pos2) 'white 'king-side))
(define wcs (determine-castling-status (Position-pp pos2) 'white))
(define bcs (determine-castling-status (Position-pp pos2) 'black))
