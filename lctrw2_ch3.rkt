#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "fen.rkt")
(require "uci-auxiliary.rkt")
(require "make-move.rkt")
(require "movement-basics.rkt")
(require "make-move.rkt")
(require "move-search.rkt")
(require "min-max-evaluation.rkt")
(require "test-common.rkt")
(require "check.rkt")
(require "legal-moves.rkt")

(define positions (positions-from-file "../krr-test/fen_lctrw2_ch3.fen"))
(define movesstrings (file->lines "solutions_lctrw2_ch3.txt"))

(: best-move (-> Position (Listof Move)))
(define (best-move pos)
  (let ([best (best-among-all-moves pos 1 evaluate-opening-position)])
    (if (empty? best) '()
        (list (car best)))))

(define first-position #t)

(: candidate-moves2 (-> Position (Listof Move)))
(define (candidate-moves2 pos)
  (if first-position
      (begin
        (set! first-position #f)
        (capturing-moves (legal-moves pos)))
      (offensive-moves pos (legal-moves pos))))

(: candidate-moves (-> Position (Listof Move)))
(define (candidate-moves pos)
  (capturing-moves (legal-moves pos)))

(: move-search (-> Position (Listof Move-evaluation)))
(define (move-search pos)
  (evaluate-moves evaluate-opening-position candidate-moves 4 pos))

(: check-solution (-> Position (Listof String) (Listof Move-evaluation)
                      String))
(define (check-solution pos move-strs solution-moves)
  (let* ([move (movestring->move pos (car move-strs))]
         [best-solutions (best-evaluations solution-moves
                                           (Position-to-move pos))])
    (cond
      [(> (length best-solutions) 1)
       (format "More than one solution found: ~a" best-solutions)]
      [(empty? best-solutions)
       (format "No solutions found")]
      [else
       (if (not (move-in-evaluations? move best-solutions))
           (format "Wrong move: ~a" best-solutions)
           (format "Ok"))])))

(: perform-test (-> (Listof Position) (Listof String) (Listof Integer)
                    Void))
(define (perform-test positions movesstrings indices)
  (for ([pos positions]
        [movesstr movesstrings] [index indices])
    (let* ([movestrings (string-split movesstr)]
           [calculated-moves (move-search pos)])
      (displayln (format "~a: ~a" index
                         (check-solution pos movestrings calculated-moves))))))

(perform-test positions
              movesstrings
              (range 1 (+ 1 (length positions))))

#|
(define pos4 (list-ref positions 3))
(define evs1 (move-search pos4))
(displayln evs1)

(define moves1 (moves-of-evaluations evs1))
(define strange-move (list-ref moves1 2))
(define pos4-2 (make-move pos4 strange-move))
(define evs2 (move-search pos4-2))
(displayln evs2)
|#
