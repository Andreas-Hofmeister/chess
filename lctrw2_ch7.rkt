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
(require "position-info-v1.rkt")
(require "attacks-defenses-v1.rkt")
(require "min-max-evaluation.rkt")
(require "test-common.rkt")
(require "check.rkt")
(require "legal-moves.rkt")

(define positions (positions-from-file "../krr-test/fen_lctrw2_ch7.fen"))
(define movesstrings (file->lines "solutions_lctrw2_ch7.txt"))

(define test1 (pos-from-fen "2bqk1br/r1pPppK1/3R1B2/PN1B4/p1RQ1n2/2p3P1/P1P2P1P/6N1 w k - 0 1"))
(define test2 (pos-from-fen "rn1qkbn1/pppppppN/2b5/3P1B2/4P3/3Q1B2/PPP1P1PP/RN2KB1R w KQq - 0 1"))
(define test3 (pos-from-fen "rn1qkbnr/ppp1pppp/2b5/3p4/4P3/5B2/PPPP1PQP/RNB1K1NR w KQkq - 0 1"))
(define test4 (pos-from-fen "r2qkb1r/ppp1pppp/2b2n2/3p4/4P3/2N2Q2/PPPP1PBP/RNB1K2R w KQkq - 0 1"))
(define test5 (pos-from-fen "rnb1kbnr/pp1p1ppp/2p1p3/3q4/8/1B3Q2/PPPPPPPP/RNB1K1NR w KQkq - 0 1"))
(define test-initial (pos-from-fen "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"))

;(define testpp (Position-pp test-initial))
;(define attacks (attacks-of-pp testpp))  
;(displayln (attacks->string attacks))
;(define defenses (defenses-of-pp testpp))
;(displayln (defenses->string defenses))
;(define sorted-attacks (sort-attacks-by-target (Attacks-white attacks)))
;(define sorted-defenses (sort-defenses-by-target (Defenses-black defenses)))
;(define d5-attacks (sort-attacks-by-piece-value (hash-ref sorted-attacks (Square-location 4 3))))
;(define d5-defenses (sort-defenses-by-piece-value (hash-ref sorted-defenses (Square-location 4 3))))
;(displayln (attack-list->string d5-attacks))
;(displayln (defense-list->string d5-defenses))
;(displayln (sorted-attacks->string sorted-attacks))
;(displayln (sorted-defenses->string sorted-defenses))
;(define possibly-en-prise (locations-with-possibly-en-prise-piece testpp))
;(for ([loc possibly-en-prise])
;  (displayln (square-location->string loc)))

(: candidate-moves (-> Position (Listof Move)))
(define (candidate-moves pos)
  (cond
    [(in-check? pos (Position-to-move pos)) (legal-moves pos)]
    [(empty? (Pos-info-en-prise (make-empty-pos-info pos))) '()]
    [else
     (filter (lambda ([move : Move])
               (or (capturing-move? move)
                   (puts-opponent-in-check? pos move)))
             (legal-moves pos))]))

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

(define positions-to-be-tested positions)
(define movesstrings-to-be-tested movesstrings)
(define indices-to-be-tested (range 1 (+ 1 (length positions))))

#|
(define positions-to-be-tested (list (list-ref positions 6)))
(define movesstrings-to-be-tested (list (list-ref movesstrings 6)))
(define indices-to-be-tested (list 7))
|#
(perform-test positions-to-be-tested
              movesstrings-to-be-tested
              indices-to-be-tested)

