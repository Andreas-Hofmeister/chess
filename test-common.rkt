#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "legal-moves.rkt")
(require "make-move.rkt")
(require "move-search.rkt")
(require "check.rkt")
(require "fen.rkt")
(require "uci-auxiliary.rkt")
(require "min-max-evaluation.rkt")
(provide (all-defined-out))

(: move-evaluations-cmp-string (-> Move (Listof Move-evaluation) String))
(define (move-evaluations-cmp-string move evs)
  (cond
    [(empty? evs) "No move found"]
    [(= 1 (length evs)) (if (move-evaluation-eq? move (car evs))
                            "ok"
                            (format "mismatch: ~a vs. ~a" move (car evs)))]
    [else (format "Too many candidate moves found: ~a" evs)]))

(: move-in-evaluations? (-> Move (Listof Move-evaluation) Boolean))
(define (move-in-evaluations? move evs)
  (exists-in evs (lambda ([ev : Move-evaluation])
                   (move-evaluation-eq? move ev))))

(: move-in-evaluations-string (-> Move (Listof Move-evaluation) String))
(define (move-in-evaluations-string move evs)
  (if (move-in-evaluations? move evs)
      "ok"
      "Move not found"))

(: forced-mate-move-search (-> Position Integer (Listof Move-evaluation)))
(define (forced-mate-move-search pos depth)
  (forced-mate-moves (forced-mate-search depth pos)))
