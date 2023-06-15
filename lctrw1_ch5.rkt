#lang typed/racket
(require racket/match)

(require "fen.rkt")
(require "uci-auxiliary.rkt")
(require "test-common.rkt")

(define positions (positions-from-file "../krr-test/fen_lctrw1_ch5.fen"))

(define movestrings (file->lines "solutions_lctrw1_ch5.txt"))

(for ([pos positions] [movestr movestrings] [index (range 1 (+ 1 (length positions)))])
  (let* ([move (movestring->move pos movestr)]
         [calculated-moves (forced-mate-move-search pos 1)])
    (displayln (format "~a: ~a" index (move-evaluations-cmp-string move calculated-moves)))))

