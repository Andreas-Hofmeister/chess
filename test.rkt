#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "legal-moves.rkt")
(require "make-move.rkt")
(require "move-search.rkt")
(require "check.rkt")
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

(define castle-pos (pos-from-fen "r3kb1r/p2qp1pp/2p1b3/1p1pPp2/8/1BP1B3/P1P2PPP/R2Q1RK1 b qk - 0 1"))

(define cp-moves (legal-moves castle-pos))
(define evs (evaluate-moves evaluate-opening-position legal-moves 2 castle-pos))

(define pos3 (make-initial-position))
(define evs2 (evaluate-moves evaluate-opening-position legal-moves 1 pos3))
(define ev (evaluate-opening-position pos3))
(define e2e4 (Double-step (Square-location 1 4) (Square-location 3 4)))
(define d2d4 (Double-step (Square-location 1 3) (Square-location 3 3)))
(define pos4 (make-move pos3 e2e4))
(define pos5 (make-move pos3 d2d4))
(define ev5 (evaluate-opening-position pos5))
(define pp4 (Position-pp pos4))
(define pp5 (Position-pp pos5))

; Aperturas 1
; Exercise 1
(define ap1ex1 (pos-from-fen "r1bqkb1r/pppp1ppp/2n2n2/4p3/2B1P3/3P1N/PPP2PPP/RNBQK2R b QKqk - 0 1"))
(define ap1ex1-A (make-move ap1ex1 (From-to-move (Square-location 7 5) (Square-location 4 2))))
(define ap1ex1-B (make-move ap1ex1 (From-to-move (Square-location 5 2) (Square-location 4 0))))
(define ap1ex1-C (make-move ap1ex1 (From-to-move (Square-location 7 5) (Square-location 3 1))))
(define answer-ap1ex1 (map evaluate-opening-position (list ap1ex1-A ap1ex1-B ap1ex1-C)))

; Exercise 2
(define ap1ex2 (pos-from-fen "rnbq1rk1/pp2bppp/2p2n2/3p2B1/3P4/2N1PN2/PP3PPP/R2QKB1R w KQ - 0 1"))
(define ap1ex2-A (make-move ap1ex2 (From-to-move (Square-location 0 5) (Square-location 2 3))))
(define ap1ex2-B (make-move ap1ex2 (From-to-move (Square-location 0 3) (Square-location 3 0))))
(define ap1ex2-C (make-move ap1ex2 (From-to-move (Square-location 1 1) (Square-location 2 1))))
(define answer-ap1ex2 (map evaluate-opening-position (list ap1ex2-A ap1ex2-B ap1ex2-C)))

; Exercise 3
(define ap1ex3 (pos-from-fen "r2q1rk1/ppp1bppp/2n1pn2/3p1b2/3P1B2/2P1PN2/PP1NBPPP/R2QK2R w KQ - 0 1"))
(define ap1ex3-A (make-move ap1ex3 (From-to-move (Square-location 1 4) (Square-location 4 1))))
(define ap1ex3-B (make-move ap1ex3 (Castle 'white 'king-side)))
(define ap1ex3-C (make-move ap1ex3 (From-to-move (Square-location 1 3) (Square-location 2 1))))
(define answer-ap1ex3 (map evaluate-opening-position (list ap1ex3-A ap1ex3-B ap1ex3-C)))

; Exercise 4
(define ap1ex4 (pos-from-fen "r2qkb1r/pp3ppp/2n1pn2/2pp4/3P1Bb1/2P1PN2/PP2BPPP/RN1QK2R w KQkq - 0 1"))
(define ap1ex4-A (make-move ap1ex4 (From-to-move (Square-location 3 5) (Square-location 4 6))))
(define ap1ex4-B (make-move ap1ex4 (From-to-move (Square-location 0 1) (Square-location 2 0))))
(define ap1ex4-C (make-move ap1ex4 (From-to-move (Square-location 0 1) (Square-location 1 3))))
(define answer-ap1ex4 (map evaluate-opening-position (list ap1ex4-A ap1ex4-B ap1ex4-C)))

; Exercise 5
(define ap1ex5 (pos-from-fen "rn2kb1r/ppp2ppp/4pn/q/2BP2b/2N2N/PPP2PPP/R1BQK2R w KQkq - 0 1"))
(define ap1ex5-A (make-move ap1ex5 (Castle 'white 'king-side)))
(define ap1ex5-B (make-move ap1ex5 (From-to-move (Square-location 3 2) (Square-location 4 1))))
(define ap1ex5-C (make-move ap1ex5 (From-to-move (Square-location 1 0) (Square-location 2 0))))
(define answer-ap1ex5 (map evaluate-opening-position
                           (list ap1ex5-A
                                 ap1ex5-B
                                 ap1ex5-C)))

; Exercise 6
(define ap1ex6 (pos-from-fen "r2q1rk1/1bp1bppp/p1np1n2/1p2p3/4P3/1BP2N1P/PP1P1PP1/RNBQR1K1 w - - 0 1"))
(define ap1ex6-A (make-move ap1ex6 (From-to-move (Square-location 2 5) (Square-location 4 6))))
(define ap1ex6-B (make-move ap1ex6 (From-to-move (Square-location 1 3) (Square-location 3 3))))
(define ap1ex6-C (make-move ap1ex6 (From-to-move (Square-location 1 6) (Square-location 3 6))))
(define answer-ap1ex6 (map evaluate-opening-position
                           (list ap1ex6-A
                                 ap1ex6-B
                                 ap1ex6-C)))


(define pos-k0skV (pos-from-fen "r1b4r/p5Q1/1q1kp3/1p1pn3/3b4/2N3P1/PP3P1P/2R2RK1 w - - 4 23"))

