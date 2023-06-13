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

(: move-search (-> Position (Listof Move-evaluation)))
(define (move-search pos)
  (forced-mate-moves (forced-mate-search 1 pos)))

(define positions (positions-from-file "../krr-test/fen_lctrw1_ch2.fen"))

(define movestrings (file->lines "solutions_lctrw1_ch2.txt"))

(for ([pos positions] [movestr movestrings] [index (range 1 (+ 1 (length positions)))])
  (let* ([move (movestring->move pos movestr)]
         [calculated-moves (move-search pos)])
    (displayln (format "~a: ~a" index (move-evaluations-cmp-string move calculated-moves)))))

