#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "legal-moves.rkt")
(require "make-move.rkt")
(require "move-search.rkt")
(require "check.rkt")
(require "fen.rkt")

;; Forced checkmates
(define fcm1 (pos-from-fen "6k1/8/6KQ/8/8/2q5/8/8 w - - 0 1"))
(define fcm2 (pos-from-fen "5rk1/8/7P/7Q/8/8/8/7K w - - 0 1"))
(define fcm3 (pos-from-fen "2q5/1k6/8/8/8/4Q3/5B2/7K w - - 0 1"))
(define fcm4 (pos-from-fen "5k2/8/8/5N2/8/6Q1/3q4/6K1 w - - 0 1"))
(define fcm5 (pos-from-fen "6R1/ppk5/7R/2p4b/3p4/8/PPPB1r2/2K5 b - - 0 1"))
(define fcm6 (pos-from-fen "r2br2k/p1qn2p1/1p2Qn1p/2p5/3P1P1N/P1PB4/1P1B2PP/3R1RK1 w - - 0 1"))
;(define fcm7 (pos-from-fen ""))
;(define fcm8 (pos-from-fen ""))
;(define fcm9 (pos-from-fen ""))

(define fcm1evs (forced-mate-search 3 fcm1))
(define fcm2evs (forced-mate-search 3 fcm2))
(define fcm3evs (forced-mate-search 3 fcm3))
(define fcm4evs (forced-mate-search 3 fcm4))
;(define fcm5evs (forced-mate-search 9 fcm5))
;takes a long time:
;(define fcm6evs (forced-mate-search 11 fcm6))


;(define fcmt1pos (pos-from-fen "q4r1k/5p1p/p2pp2Q/1p2b3/8/2P2R2/P1P3RP/7K w - - 0 1"))
;(define fcmt1 (forced-checkmate-threats fcmt1pos (legal-moves fcmt1pos)))

; Forced checkmate threats
(define fcmt2pos (pos-from-fen "r2r2k1/pb3ppp/1p6/2p3q1/P2p2B1/3P2PP/1PP2P2/R2QR1K1 b - - 0 1"))
(define fcmt2 (forced-checkmate-threats fcmt2pos (legal-moves fcmt2pos)))

