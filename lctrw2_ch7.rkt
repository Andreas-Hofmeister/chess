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

(define positions (positions-from-file "../krr-test/fen_lctrw2_ch7.fen"))
(define movesstrings (file->lines "solutions_lctrw2_ch7.txt"))

(struct Attack ([attacker-location : Square-location]
                [attacker-piece : Piece]
                [attacker-color : Color]
                [target-location : Square-location]
                [target-piece : Piece]
                [target-color : Color]
                [directness : Integer]))

(: attacks-in-direction (-> Piece-placements
                            Square-location
                            Square-location
                            Integer
                            Color
                            Piece
                            Integer Integer
                            (Setof Piece)
                            (Listof Attack)))
(define (attacks-in-direction pp attacker-loc current-loc current-directness color piece dir-x dir-y extension-pieces)
  (if (not (location-valid? current-loc)) '()
      (match (get-square-by-location pp current-loc)
        ['empty-square (attacks-in-direction pp attacker-loc
                                             (add-to-square-location current-loc dir-x dir-y)
                                             current-directness
                                             color piece dir-x dir-y extension-pieces)]
        [(Occupied-square target-color target-piece)
         #:when (eq? target-color color)
         (if (set-member? extension-pieces target-piece)
             (attacks-in-direction pp attacker-loc
                                   (add-to-square-location current-loc dir-x dir-y)
                                   (+ current-directness 1)
                                   color piece dir-x dir-y extension-pieces)
             '())]
        [(Occupied-square target-color target-piece)
         (list (Attack attacker-loc piece color current-loc target-piece target-color current-directness))])))

(: attacks-by-queen (-> Piece-placements Square-location Color
                        (Listof Attack)))
(define (attacks-by-queen pp loc color)
  (append (attacks-in-direction pp loc (add-to-square-location loc 1 0) 0 color 'queen 1 0 (set 'queen 'rook))
          (attacks-in-direction pp loc (add-to-square-location loc -1 0) 0 color 'queen -1 0 (set 'queen 'rook))
          (attacks-in-direction pp loc (add-to-square-location loc 0 1) 0 color 'queen 0 1 (set 'queen 'rook))
          (attacks-in-direction pp loc (add-to-square-location loc 0 -1) 0 color 'queen 0 -1 (set 'queen 'rook))
          (attacks-in-direction pp loc (add-to-square-location loc 1 1) 0 color 'queen 1 1 (set 'queen 'bishop))
          (attacks-in-direction pp loc (add-to-square-location loc -1 -1) 0 color 'queen -1 -1 (set 'queen 'bishop))
          (attacks-in-direction pp loc (add-to-square-location loc 1 -1) 0 color 'queen 1 -1 (set 'queen 'bishop))
          (attacks-in-direction pp loc (add-to-square-location loc -1 1) 0 color 'queen -1 1 (set 'queen 'bishop))))

(: candidate-moves (-> Position (Listof Move)))
(define (candidate-moves pos)
  (if (in-check? pos (Position-to-move pos))
      (legal-moves pos)
      (filter (lambda ([move : Move])
                (or (capturing-move? move)
                    (puts-opponent-in-check? pos move)))
              (legal-moves pos))))

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

#|
(define positions-to-be-tested positions)
(define movesstrings-to-be-tested movesstrings)
(define indices-to-be-tested (range 1 (+ 1 (length positions))))
|#

(define positions-to-be-tested (list (list-ref positions 6)))
(define movesstrings-to-be-tested (list (list-ref movesstrings 6)))
(define indices-to-be-tested (list 7))

(perform-test positions-to-be-tested
              movesstrings-to-be-tested
              indices-to-be-tested)
