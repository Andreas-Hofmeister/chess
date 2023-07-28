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

(: defends-en-prise? (-> Position Square-location Move Boolean))
(define (defends-en-prise? pos loc move)
  (equal? loc (from-of-move move)))

(: checkmate-defensive-moves (-> Position (Listof Move) (Listof Move)))
(define (checkmate-defensive-moves pos moves)
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
    (not (empty? new-en-prise))))

(: equivalent-trade? (-> Piece (Listof Attack) (Listof Defense) Boolean))
(define (equivalent-trade? piece attacks defenses)
  (let* ([balances (sequence-of-material-gain piece
                                              (sort-attacks-by-piece-value attacks)
                                              (sort-defenses-by-piece-value defenses)
                                              true
                                              0)]
         [len (length balances)])
    (or (exists-in (range len)
                   (lambda ([i : Integer])
                     (and (odd? i)
                          (= (list-ref balances i) 0))))
        (and (> len 0)
             (= (list-ref balances (- len 1)) 0)))))

(: locations-with-equivalent-trades (-> Piece-placements (Listof Square-location)))
(define (locations-with-equivalent-trades pp)
  (let* ([attacks (attacks-of-pp pp)]
         [defenses (defenses-of-pp pp)]
         [sorted-white-attacks (sort-attacks-by-target (Attacks-white attacks))]
         [sorted-black-attacks (sort-attacks-by-target (Attacks-black attacks))]
         [sorted-white-defenses (sort-defenses-by-target (Defenses-white defenses))]
         [sorted-black-defenses (sort-defenses-by-target (Defenses-black defenses))]
         [locs : (Listof Square-location) '()])
    (for ([loc valid-locations])
       (match (get-square-by-location pp loc)
         [(Occupied-square color piece)
          (let* ([sorted-attacks : (HashTable Square-location (Listof Attack))
                                 (if (eq? color 'white) sorted-black-attacks
                                     sorted-white-attacks)]
                 [sorted-defenses : (HashTable Square-location (Listof Defense))
                                  (if (eq? color 'white) sorted-white-defenses
                                      sorted-black-defenses)]
                 [piece-attacks : (Listof Attack) (hash-ref sorted-attacks loc (lambda () '()))]
                 [piece-defenses : (Listof Defense) (hash-ref sorted-defenses loc (lambda () '()))])
            (when (equivalent-trade? piece piece-attacks piece-defenses)
              (set! locs (cons loc locs))))]
         [_ 'nil]))
    locs))

(: candidate-moves (-> Position Integer (Listof Move)))
(define (candidate-moves pos depth)
  (cond
    [(in-check? pos (Position-to-move pos)) (legal-moves pos)]
    [else
     (let* ([moves (legal-moves pos)]
            [enemies-en-prise (locations-occupied-by-enemy-piece
                               (Position-pp pos)
                               (locations-with-possibly-en-prise-piece (Position-pp pos))
                               (Position-to-move pos))]
            [offensive-moves
             (filter (lambda ([move : Move])
                       (or (capturing-move? move)
                           (puts-opponent-in-check? pos move)
                           (puts-en-prise? pos move)))
                     moves)]
            [cm-def-moves (defensive-moves pos moves)]
            [en-prise (locations-occupied-by-friendly-piece (Position-pp pos)
                                                            (locations-with-possibly-en-prise-piece (Position-pp pos))
                                                            (Position-to-move pos))]
            [ep-def-moves (filter (lambda ([move : Move])
                                    (exists-in en-prise
                                     (lambda ([loc : Square-location])
                                       (defends-en-prise? pos loc move))))
                                  moves)])
       (remove-duplicates (append offensive-moves cm-def-moves ep-def-moves)))]))

(: optional-stop? (-> Position Integer Boolean))
(define (optional-stop? pos depth)
#f)
;  (empty? (locations-with-possibly-en-prise-piece (Position-pp pos))))

(: move-search (-> Position (Listof Move-evaluation)))
(define (move-search pos)
  (evaluate-moves-with-optional-stopping evaluate-opening-position candidate-moves optional-stop? 4 pos))

(: evs->string (-> (Listof Move-evaluation) String))
(define (evs->string evs)
  (let ([moves (moves-of-evaluations evs)]
        [vs (map move-evaluation->integer evs)]
        [result : (Listof String) '()])
    (for ([move moves]
          [v vs])
      (set! result (cons (format "~a: ~a" (move->uci-string move) v) result)))
    (string-join (reverse result) ", ")))

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
           (format "Wrong move: ~a"
                   (evs->string (sort-evaluations solution-moves (Position-to-move pos))))
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
(define positions-to-be-tested (take positions 20))
(define movesstrings-to-be-tested (take movesstrings 20))
(define indices-to-be-tested (range 1 21))
|#
#|
(define positions-to-be-tested (list (list-ref positions 7)))
(define movesstrings-to-be-tested (list (list-ref movesstrings 7)))
(define indices-to-be-tested (list 8))

(perform-test positions-to-be-tested
              movesstrings-to-be-tested
              indices-to-be-tested)
|#


