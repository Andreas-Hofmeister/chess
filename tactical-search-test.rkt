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
(define pos2 (pos-from-fen "3rrbk1/ppn3pp/2pn1p2/3p3q/P1PP4/1P1QNN1P/4R1PB/4R1K1 w - - 0 1"))
; Puzzle #I4bSW on lichess.org (forks the king and a rook with a queen to capture the rook)
(define pos3 (pos-from-fen "3R4/5pk1/1n1p2p1/pPpP4/5PP1/1P1Q4/5K2/7q b - - 6 40"))
; Puzzle #wvYno on lichess.org (capture, checkmate threat)
(define pos4 (pos-from-fen "rn3rk1/1p3npp/2p1Q3/p2p4/4P3/2N5/PPq3PP/R4R1K w - - 0 19"))
; Puzzle #uCFHs on lichess.org (mate in 4)
(define pos5 (pos-from-fen "7R/8/1k2p2P/1p1pB3/3P4/K3n1P1/6r1/8 b - - 2 39"))
; Puzzle #JZXZt on lichess.org (threaten checkmate, various captures)
(define pos6 (pos-from-fen "1n6/3q1p1k/2p2r1P/4r3/1b1pPN2/pP1P1Q2/B1P2P2/2K4R w - - 2 29"))
; Puzzle #zVjsh on lichess.org (threaten checkmate twice to capture the queen)
(define pos7 (pos-from-fen "r4k1r/ppp2pp1/3p3p/4nP2/6nq/1BN1P2P/PPP1Q1P1/R4RK1 b - - 0 14"))
; Puzzle #853bE on lichess.org (threaten a fork)
(define pos8 (pos-from-fen "2k4r/ppp1n3/4Np2/8/3b1P2/3r4/PP4PP/1RB2R1K b - - 4 21"))
; Puzzle #ci7x0 on lichess.org (defend against checkmate, then counterattack)
(define pos9 (pos-from-fen "3r1r1R/ppp1p1k1/6P1/5p2/4N2Q/5P2/2q1K3/3n2N1 w - - 0 27"))
; Exercise 2 for chapter "Cómo encontrar las combinaciones" (p. 256)
(define pos10 (pos-from-fen "q4r1k/5p1p/p2pp2Q/1p2b3/8/2P2R2/P1P4P/6RK w - - 0 1"))



(define m3 (legal-moves pos3))
(define t3 (forced-checkmate-threats pos3 m3))
(define fcm5evs (forced-mate-search 7 pos5))
