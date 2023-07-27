#lang typed/racket
(require racket/match)
(require racket/set)

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

(define positions (positions-from-file "../krr-test/fen_lctrw2_ch8.fen"))
(define movesstrings (file->lines "solutions_lctrw2_ch8.txt"))

;(: defends-en-prise (-> Position Square-location Move Boolean))
;(define (defends-en-prise

(: defensive-moves (-> Position (Listof Move) (Listof Move)))
(define (defensive-moves pos moves)
  (if (in-check? pos (Position-to-move pos)) moves
      (let* ([rev-pos (switch-to-move pos)]
             [rev-moves (legal-moves rev-pos)]
             [checkmate-threats (moves-of-evaluations (forced-mate-moves (forced-mate-search 1 rev-pos)))]
             [compute-defenses (lambda ([move : Move])
                                 (defensive-moves-for-checkmate-threat pos move moves))]
             [checkmate-threat-defenses (flatten-moves (map compute-defenses checkmate-threats))]
             [result checkmate-threat-defenses])
        result)))

(: puts-en-prise? (-> Position Move Boolean))
(define (puts-en-prise? pos move)
  (let* ([en-prise-now (locations-with-possibly-en-prise-piece (Position-pp pos))]
         [new-pos (make-move pos move)]
         [en-prise-then (locations-with-possibly-en-prise-piece (Position-pp new-pos))]
         [enemies-en-prise-then (locations-occupied-by-enemy-piece (Position-pp new-pos)
                                                                   en-prise-then
                                                                   (Position-to-move pos))]
         [new-en-prise (filter (lambda ([loc : Square-location])
                                 (not (exists-in en-prise-now
                                                 (lambda ([loc2 : Square-location]) (equal? loc loc2)))))
                               enemies-en-prise-then)])
    (displayln (format "Before: ~a, After: ~a"
                       (map square-location->string en-prise-now)
                       (map square-location->string en-prise-then)))
    (not (empty? new-en-prise))))

(: candidate-moves (-> Position Integer (Listof Move)))
(define (candidate-moves pos depth)
  (cond
    [(in-check? pos (Position-to-move pos)) (legal-moves pos)]
    ;[(empty? (locations-with-possibly-en-prise-piece (Position-pp pos))) '()]
    [else
     (let* ([moves (legal-moves pos)]
            [offensive-moves
             (filter (lambda ([move : Move])
                       (or (capturing-move? move)
                           (puts-opponent-in-check? pos move)))
                     moves)]
            [def-moves (defensive-moves pos moves)])
       (remove-duplicates (append offensive-moves def-moves)))]))

(: optional-stop? (-> Position Integer Boolean))
(define (optional-stop? pos depth) #f)
;  (empty? (locations-with-possibly-en-prise-piece (Position-pp pos))))

(: move-search (-> Position (Listof Move-evaluation)))
(define (move-search pos)
  (evaluate-moves-with-optional-stopping evaluate-opening-position candidate-moves optional-stop? 4 pos))

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
           (format "Wrong move: ~a" solution-moves)
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
#|
(define positions-to-be-tested positions)
(define movesstrings-to-be-tested movesstrings)
(define indices-to-be-tested (range 1 (+ 1 (length positions))))
|#
#|
(define positions-to-be-tested (take positions 15))
(define movesstrings-to-be-tested (take movesstrings 15))
(define indices-to-be-tested (range 1 16))
|#

(define positions-to-be-tested (list (list-ref positions 16)))
(define movesstrings-to-be-tested (list (list-ref movesstrings 16)))
(define indices-to-be-tested (list 17))
#|
(perform-test positions-to-be-tested
              movesstrings-to-be-tested
              indices-to-be-tested)
|#

