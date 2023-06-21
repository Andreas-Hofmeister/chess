#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "fen.rkt")
(require "uci-auxiliary.rkt")
(require "make-move.rkt")
(require "movement-basics.rkt")
(require "move-search.rkt")
(require "min-max-evaluation.rkt")
(require "test-common.rkt")

(define positions (positions-from-file "../krr-test/fen_lctrw1_ch10.fen"))
(define movesstrings (file->lines "solutions_lctrw1_ch10.txt"))

(: defensive-moves-for-checkmate-threat (-> Position Move (Listof Move)
                                            (Listof Move)))
(define (defensive-moves-for-checkmate-threat pos threatened-move all-moves)
  (filter (lambda ([move : Move])
            (or (king-move? pos move)
                (move-by-piece-adjacent-to-king? pos move)
                (move-defends-square? pos move (to-of-move threatened-move))
                (move-blocks-move? pos move threatened-move)
                (puts-opponent-in-check? pos move)))
          all-moves))

#|
(define (move-search pos)
  (let ([forced-by-successive-checks (forced-mate-move-search pos 3)])
    (if (not (empty? forced-by-successive-checks))
        forced-by-successive-checks
|#      

(: check-solution (-> Position (Listof String) (Listof Move-evaluation)
                      String))
(define (check-solution pos move-strs solution-moves)
  (let* ([move (movestring->move pos (car move-strs))]
         [pos2 (make-move pos move)]
         [reply (movestring->move pos2 (car (cdr move-strs)))]
         [pos3 (make-move pos2 reply)]
         [move2 (movestring->move pos3 (car (cdr (cdr move-strs))))])
    (if (not (move-in-evaluations? move solution-moves))
        (format "First move not found: ~a" solution-moves)
        (let ([mate-in-one-evs (forced-mate-move-search pos3 1)])
          (if (move-in-evaluations? move2 mate-in-one-evs)
              (format "Ok")
              (format "Second move not found: ~a" mate-in-one-evs))))))

(: perform-test (-> (Listof Position) (Listof String) (Listof Integer)
                    Void))
(define (perform-test positions movesstrings indices)
  (for ([pos positions]
        [movesstr movesstrings] [index indices])
    (let* ([movestrings (string-split movesstr)]
           [calculated-moves (forced-mate-move-search pos 3)])
      (displayln (format "~a: ~a" index
                         (check-solution pos movestrings calculated-moves))))))
#|
(perform-test positions
              movesstrings
              (range 1 (+ 1 (length positions))))
|#

(define locs1 (locations-between (Square-location 0 0) (Square-location 2 3)))
(displayln locs1)

