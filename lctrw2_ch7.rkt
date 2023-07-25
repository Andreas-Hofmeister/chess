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
                [directness : Integer])
  #:transparent)

(: attacks-in-direction (-> Piece-placements
                            Square-location
                            Square-location
                            Integer
                            Color
                            Piece
                            Integer Integer
                            (HashTable Piece Integer)
                            Integer
                            (Listof Attack)))
(define (attacks-in-direction pp attacker-loc current-loc current-directness color piece dir-x dir-y extension-pieces fuel)
  (if (or (not (location-valid? current-loc)) (= 0 fuel)) '()
      (match (get-square-by-location pp current-loc)
        ['empty-square (attacks-in-direction pp attacker-loc
                                             (add-to-square-location current-loc dir-x dir-y)
                                             current-directness
                                             color piece dir-x dir-y extension-pieces (- fuel 1))]
        [(Occupied-square target-color target-piece)
         #:when (eq? target-color color)
         (if (hash-has-key? extension-pieces target-piece)
             (attacks-in-direction pp attacker-loc
                                   (add-to-square-location current-loc dir-x dir-y)
                                   (+ current-directness 1)
                                   color piece dir-x dir-y extension-pieces (min (- fuel 1)
                                                                                 (hash-ref extension-pieces target-piece)))
             '())]
        [(Occupied-square target-color target-piece)
         (list (Attack attacker-loc piece color current-loc target-piece target-color current-directness))])))

(: attacks-in-directions (-> Piece-placements
                            Square-location
                            Color
                            Piece
                            (Listof (Pairof Integer Integer))
                            (HashTable Piece Integer)
                            (Listof Attack)))
(define (attacks-in-directions pp attacker-loc color piece dir-list extension-pieces)
  (if (empty? dir-list) '()
      (let* ([dir (car dir-list)]
             [delta-x (car dir)]
             [delta-y (cdr dir)])
        (append (attacks-in-direction pp attacker-loc (add-to-square-location attacker-loc delta-x delta-y)
                                      0 color piece delta-x delta-y extension-pieces 8)
                (attacks-in-directions pp attacker-loc color piece (cdr dir-list) extension-pieces)))))

(define up-down-left-right-dirs (list (cons 1 0) (cons -1 0) (cons 0 1) (cons 0 -1)))
(define diagonal-up-dirs (list (cons 1 1) (cons -1 1)))
(define diagonal-down-dirs (list (cons 1 -1) (cons -1 -1)))
(define up-down-left-right-extensions (hash 'queen 8 'rook 8))
(: diagonal-up-extensions (-> Color (HashTable Piece Integer)))
(define (diagonal-up-extensions color)
  (if (eq? color 'white) (hash 'queen 8 'bishop 8 'pawn 1)
      (hash 'queen 8 'bishop 8)))
(: diagonal-down-extensions (-> Color (HashTable Piece Integer)))
(define (diagonal-down-extensions color)
  (if (eq? color 'white) (hash 'queen 8 'bishop 8)
      (hash 'queen 8 'bishop 8 'pawn 1)))
(define knight-jump-deltas (list (cons 1 2) (cons -1 2) (cons -2 1) (cons -2 -1)
                                 (cons -1 -2) (cons 1 -2) (cons 2 -1) (cons 2 1)))
(: pawn-deltas (-> Color (Listof (Pairof Integer Integer))))
(define (pawn-deltas color)
  (let ([delta-y (if (eq? color 'white) 1 -1)])
    (list (cons 1 delta-y) (cons -1 delta-y))))
(define king-deltas (list (cons 1 0) (cons 1 1) (cons 0 1) (cons -1 1)
                          (cons -1 0) (cons -1 -1) (cons 0 -1) (cons 1 -1)))
    
(: attacks-by-queen (-> Piece-placements Square-location Color
                        (Listof Attack)))
(define (attacks-by-queen pp loc color)
  (append (attacks-in-directions pp loc color 'queen up-down-left-right-dirs up-down-left-right-extensions)
          (attacks-in-directions pp loc color 'queen diagonal-up-dirs (diagonal-up-extensions color))
          (attacks-in-directions pp loc color 'queen diagonal-down-dirs (diagonal-down-extensions color))))

(: attacks-by-rook (-> Piece-placements Square-location Color
                       (Listof Attack)))
(define (attacks-by-rook pp loc color)
  (attacks-in-directions pp loc color 'rook up-down-left-right-dirs up-down-left-right-extensions))

(: attacks-by-bishop (-> Piece-placements Square-location Color
                         (Listof Attack)))
(define (attacks-by-bishop pp loc color)
  (append (attacks-in-directions pp loc color 'bishop diagonal-up-dirs (diagonal-up-extensions color))
          (attacks-in-directions pp loc color 'bishop diagonal-down-dirs (diagonal-down-extensions color))))

(: one-step-attack (-> Piece-placements Square-location Piece Color Integer Integer
                       (Listof Attack)))
(define (one-step-attack pp loc piece color delta-x delta-y)
  (let ([target-loc (add-to-square-location loc delta-x delta-y)])
    (if (location-valid? target-loc)
        (match (get-square-by-location pp target-loc)
          [(Occupied-square target-color target-piece)
           #:when (not (eq? target-color color))
           (list (Attack loc piece color target-loc target-piece target-color 0))]
          [_ '()])
        '())))

(: one-step-attacks (-> Piece-placements Square-location Piece Color
                        (Listof (Pairof Integer Integer))
                        (Listof Attack)))
(define (one-step-attacks pp loc piece color deltas)
  (: iter (-> (Listof (Pairof Integer Integer)) (Listof Attack)))
  (define (iter deltas)
    (if (empty? deltas) '()
        (append (one-step-attack pp loc piece color (car (car deltas)) (cdr (car deltas)))
                (iter (cdr deltas)))))
  (iter deltas))

(: attacks-by-knight (-> Piece-placements Square-location Color
                         (Listof Attack)))
(define (attacks-by-knight pp loc color)
  (one-step-attacks pp loc 'knight color knight-jump-deltas))

(: attacks-by-pawn (-> Piece-placements Square-location Color
                       (Listof Attack)))
(define (attacks-by-pawn pp loc color)
  (one-step-attacks pp loc 'pawn color (pawn-deltas color)))

(: attacks-by-king (-> Piece-placements Square-location Color
                       (Listof Attack)))
(define (attacks-by-king pp loc color)
  (one-step-attacks pp loc 'king color king-deltas))

(: attacks-of-piece (-> Piece-placements Square-location Piece Color
                        (Listof Attack)))
(define (attacks-of-piece pp loc piece color)
  (match piece
    ['pawn (attacks-by-pawn pp loc color)]
    ['rook (attacks-by-rook pp loc color)]
    ['bishop (attacks-by-bishop pp loc color)]
    ['knight (attacks-by-knight pp loc color)]
    ['queen (attacks-by-queen pp loc color)]
    ['king (attacks-by-king pp loc color)]))

(struct Attacks ([white : (Listof Attack)]
                 [black : (Listof Attack)])
  #:transparent)

(: attacks-of-pp (-> Piece-placements Attacks))
(define (attacks-of-pp pp)
  (let ([white-attacks : (Listof Attack) '()]
        [black-attacks : (Listof Attack) '()])
    (for ([loc valid-locations])
      (match (get-square-by-location pp loc)
        [(Occupied-square color piece)
         #:when (eq? color 'white)
         (set! white-attacks (append white-attacks (attacks-of-piece pp loc piece color)))]
        [(Occupied-square color piece)
         (set! black-attacks (append black-attacks (attacks-of-piece pp loc piece color)))]
        [_ '()]))
    (Attacks white-attacks black-attacks)))

(: attack->string (-> Attack String))
(define (attack->string attack)
  (match attack
    [(Attack a-loc a-piece a-color t-loc t-piece t-color directness)
     (format "~a ~a on ~a attacks ~a ~a on ~a (directness: ~a)"
             a-color a-piece (square-location->string a-loc)
             t-color t-piece (square-location->string t-loc) directness)]))

(: attack-list->string (-> (Listof Attack) String))
(define (attack-list->string attacks)
  (foldr (lambda ([attack : Attack] [s : String])
           (string-append (attack->string attack) "\n" s))
         ""
         attacks))

(: attacks->string (-> Attacks String))
(define (attacks->string attacks)
  (string-append "white attacks:\n" (attack-list->string (Attacks-white attacks))
                 "\nblack attacks:\n" (attack-list->string (Attacks-black attacks))))

(struct Defense ([defender-location : Square-location]
                 [defender-piece : Piece]
                 [color : Color]
                 [target-location : Square-location]
                 [target-piece : Piece]
                 [directness : Integer])
  #:transparent)

(: defenses-in-direction (-> Piece-placements
                             Square-location
                             Square-location
                             Integer
                             Color
                             Piece
                             Integer Integer
                             (HashTable Piece Integer)
                             Integer
                             (Listof Defense)))
(define (defenses-in-direction pp defender-loc current-loc current-directness color piece dir-x dir-y extension-pieces fuel)
  (if (or (not (location-valid? current-loc)) (= 0 fuel)) '()
      (match (get-square-by-location pp current-loc)
        ['empty-square (defenses-in-direction pp defender-loc
                         (add-to-square-location current-loc dir-x dir-y)
                         current-directness
                         color piece dir-x dir-y extension-pieces (- fuel 1))]
        [(Occupied-square target-color target-piece)
         #:when (eq? target-color color)
         (let ([defense (Defense defender-loc piece color current-loc target-piece current-directness)])
           (if (hash-has-key? extension-pieces target-piece)
               (cons defense
                     (defenses-in-direction pp defender-loc
                       (add-to-square-location current-loc dir-x dir-y)
                       (+ current-directness 1)
                       color piece dir-x dir-y extension-pieces (min (- fuel 1)
                                                                     (hash-ref extension-pieces target-piece))))
               (list defense)))]
        [_ '()])))

(: defenses-in-directions (-> Piece-placements
                              Square-location
                              Color
                              Piece
                              (Listof (Pairof Integer Integer))
                              (HashTable Piece Integer)
                              (Listof Defense)))
(define (defenses-in-directions pp defender-loc color piece dir-list extension-pieces)
  (if (empty? dir-list) '()
      (let* ([dir (car dir-list)]
             [delta-x (car dir)]
             [delta-y (cdr dir)])
        (append (defenses-in-direction pp defender-loc (add-to-square-location defender-loc delta-x delta-y)
                  0 color piece delta-x delta-y extension-pieces 8)
                (defenses-in-directions pp defender-loc color piece (cdr dir-list) extension-pieces)))))

(: defenses-by-queen (-> Piece-placements Square-location Color
                         (Listof Defense)))
(define (defenses-by-queen pp loc color)
  (append (defenses-in-directions pp loc color 'queen up-down-left-right-dirs up-down-left-right-extensions)
          (defenses-in-directions pp loc color 'queen diagonal-up-dirs (diagonal-up-extensions color))
          (defenses-in-directions pp loc color 'queen diagonal-down-dirs (diagonal-down-extensions color))))

(: defenses-by-rook (-> Piece-placements Square-location Color
                        (Listof Defense)))
(define (defenses-by-rook pp loc color)
  (defenses-in-directions pp loc color 'rook up-down-left-right-dirs up-down-left-right-extensions))

(: defenses-by-bishop (-> Piece-placements Square-location Color
                          (Listof Defense)))
(define (defenses-by-bishop pp loc color)
  (append (defenses-in-directions pp loc color 'bishop diagonal-up-dirs (diagonal-up-extensions color))
          (defenses-in-directions pp loc color 'bishop diagonal-down-dirs (diagonal-down-extensions color))))

(: one-step-defense (-> Piece-placements Square-location Piece Color Integer Integer
                        (Listof Defense)))
(define (one-step-defense pp loc piece color delta-x delta-y)
  (let ([target-loc (add-to-square-location loc delta-x delta-y)])
    (if (location-valid? target-loc)
        (match (get-square-by-location pp target-loc)
          [(Occupied-square target-color target-piece)
           #:when (eq? target-color color)
           (list (Defense loc piece color target-loc target-piece 0))]
          [_ '()])
        '())))

(: one-step-defenses (-> Piece-placements Square-location Piece Color
                         (Listof (Pairof Integer Integer))
                         (Listof Defense)))
(define (one-step-defenses pp loc piece color deltas)
  (: iter (-> (Listof (Pairof Integer Integer)) (Listof Defense)))
  (define (iter deltas)
    (if (empty? deltas) '()
        (append (one-step-defense pp loc piece color (car (car deltas)) (cdr (car deltas)))
                (iter (cdr deltas)))))
  (iter deltas))

(: defenses-by-knight (-> Piece-placements Square-location Color
                          (Listof Defense)))
(define (defenses-by-knight pp loc color)
  (one-step-defenses pp loc 'knight color knight-jump-deltas))

(: defenses-by-pawn (-> Piece-placements Square-location Color
                        (Listof Defense)))
(define (defenses-by-pawn pp loc color)
  (one-step-defenses pp loc 'pawn color (pawn-deltas color)))

(: defenses-by-king (-> Piece-placements Square-location Color
                        (Listof Defense)))
(define (defenses-by-king pp loc color)
  (one-step-defenses pp loc 'king color king-deltas))

(: defenses-of-piece (-> Piece-placements Square-location Piece Color
                         (Listof Defense)))
(define (defenses-of-piece pp loc piece color)
  (match piece
    ['pawn (defenses-by-pawn pp loc color)]
    ['rook (defenses-by-rook pp loc color)]
    ['bishop (defenses-by-bishop pp loc color)]
    ['knight (defenses-by-knight pp loc color)]
    ['queen (defenses-by-queen pp loc color)]
    ['king (defenses-by-king pp loc color)]))

(struct Defenses ([white : (Listof Defense)]
                  [black : (Listof Defense)])
  #:transparent)

(: defenses-of-pp (-> Piece-placements Defenses))
(define (defenses-of-pp pp)
  (let ([white-defenses : (Listof Defense) '()]
        [black-defenses : (Listof Defense) '()])
    (for ([loc valid-locations])
      (match (get-square-by-location pp loc)
        [(Occupied-square color piece)
         #:when (eq? color 'white)
         (set! white-defenses (append white-defenses (defenses-of-piece pp loc piece color)))]
        [(Occupied-square color piece)
         (set! black-defenses (append black-defenses (defenses-of-piece pp loc piece color)))]
        [_ '()]))
    (Defenses white-defenses black-defenses)))

(: defense->string (-> Defense String))
(define (defense->string attack)
  (match attack
    [(Defense d-loc d-piece color t-loc t-piece directness)
     (format "~a ~a on ~a defends ~a ~a on ~a (directness: ~a)"
             color d-piece (square-location->string d-loc)
             color t-piece (square-location->string t-loc) directness)]))

(: defense-list->string (-> (Listof Defense) String))
(define (defense-list->string defenses)
  (foldr (lambda ([defense : Defense] [s : String])
           (string-append (defense->string defense) "\n" s))
         ""
         defenses))

(: defenses->string (-> Defenses String))
(define (defenses->string defenses)
  (string-append "white defenses:\n" (defense-list->string (Defenses-white defenses))
                 "\nblack defenses:\n" (defense-list->string (Defenses-black defenses))))

(: sort-attacks-by-target (-> (Listof Attack) 
                              (HashTable Square-location (Listof Attack))))
(define (sort-attacks-by-target attacks)
  (: sorted-attacks (HashTable Square-location (Listof Attack)))
  (define sorted-attacks (make-hash))
  (: iter (-> (Listof Attack) (HashTable Square-location (Listof Attack))))
  (define (iter remaining-attacks)
    (if (empty? remaining-attacks) sorted-attacks
        (let* ([attack (car remaining-attacks)]
               [target-loc (Attack-target-location attack)]
               [attacks-so-far : (Listof Attack) (hash-ref! sorted-attacks target-loc (lambda () '()))])
          (hash-set! sorted-attacks target-loc (cons attack attacks-so-far))
          (iter (cdr remaining-attacks)))))
  (iter attacks))

(: sort-defenses-by-target (-> (Listof Defense) 
                               (HashTable Square-location (Listof Defense))))
(define (sort-defenses-by-target defenses)
  (: sorted-defenses (HashTable Square-location (Listof Defense)))
  (define sorted-defenses (make-hash))
  (: iter (-> (Listof Defense) (HashTable Square-location (Listof Defense))))
  (define (iter remaining-defenses)
    (if (empty? remaining-defenses) sorted-defenses
        (let* ([defense (car remaining-defenses)]
               [target-loc (Defense-target-location defense)]
               [defenses-so-far : (Listof Defense) (hash-ref! sorted-defenses target-loc (lambda () '()))])
          (hash-set! sorted-defenses target-loc (cons defense defenses-so-far))
          (iter (cdr remaining-defenses)))))
  (iter defenses))

(: sorted-attacks->string (-> (HashTable Square-location (Listof Attack)) String))
(define (sorted-attacks->string sorted-attacks)
  (let* ([result ""])
    (hash-for-each sorted-attacks
                   (lambda ([target-location : Square-location]
                            [attacks : (Listof Attack)])
                     (let ([target-color (Attack-target-color (car attacks))]
                           [target-piece (Attack-target-piece (car attacks))])
                       (set! result (format "~a~a ~a on ~a is attacked by:\n"
                                            (if (non-empty-string? result) (format "~a\n" result) result)
                                            target-color target-piece
                                            (square-location->string target-location)))
                       (set! result (string-append result (attack-list->string attacks))))))
    result))

(: sorted-defenses->string (-> (HashTable Square-location (Listof Defense)) String))
(define (sorted-defenses->string sorted-defenses)
  (let* ([result ""])
    (hash-for-each sorted-defenses
                   (lambda ([target-location : Square-location]
                            [defenses : (Listof Defense)])
                     (let ([target-color (Defense-color (car defenses))]
                           [target-piece (Defense-target-piece (car defenses))])
                       (set! result (format "~a~a ~a on ~a is defended by:\n"
                                            (if (non-empty-string? result) (format "~a\n" result) result)
                                            target-color target-piece
                                            (square-location->string target-location)))
                       (set! result (string-append result (defense-list->string defenses))))))
    result))

(: value-of-piece (-> Piece Integer))
(define (value-of-piece p)
  (match p
    ['queen 9]
    ['rook 5]
    ['bishop 3]
    ['knight 3]
    ['pawn 1]
    ['king 700]))

(: piece< (-> Piece Piece Boolean))
(define (piece< piece1 piece2)
  (< (value-of-piece piece1) (value-of-piece piece2)))

(: sort-attacks-by-piece-value (-> (Listof Attack) (Listof Attack)))
(define (sort-attacks-by-piece-value attacks)
  (sort attacks
        (lambda ([attack1 : Attack] [attack2 : Attack])
          (piece< (Attack-attacker-piece attack1)
                  (Attack-attacker-piece attack2)))))

(: sort-defenses-by-piece-value (-> (Listof Defense) (Listof Defense)))
(define (sort-defenses-by-piece-value defenses)
  (sort defenses
        (lambda ([defense1 : Defense] [defense2 : Defense])
          (piece< (Defense-defender-piece defense1)
                  (Defense-defender-piece defense2)))))

(: sequence-of-material-gain (-> Piece (Listof Attack) (Listof Defense) Boolean Integer
                                 (Listof Integer)))
(define (sequence-of-material-gain target-piece sorted-attacks sorted-defenses attacker-to-move material-balance-so-far)
  (cond
    [(and attacker-to-move (empty? sorted-attacks)) '()]
    [(and (not attacker-to-move) (empty? sorted-defenses)) '()]
    [attacker-to-move
     (let* ([attack (car sorted-attacks)]
            [attacking-piece (Attack-attacker-piece attack)]
            [new-balance (+ material-balance-so-far (value-of-piece target-piece))])
       (cons new-balance (sequence-of-material-gain attacking-piece
                                                    (cdr sorted-attacks)
                                                    sorted-defenses
                                                    false
                                                    new-balance)))]
    [else ; i.e. (not attacker-to-move)
     (let* ([defense (car sorted-defenses)]
            [defending-piece (Defense-defender-piece defense)]
            [new-balance (- material-balance-so-far (value-of-piece target-piece))])
       (cons new-balance (sequence-of-material-gain defending-piece
                                                    sorted-attacks
                                                    (cdr sorted-defenses)
                                                    true
                                                    new-balance)))]))


#|
white pawn on e4 attacks black pawn on d5 (directness: 0)
white knight on c3 attacks black pawn on d5 (directness: 0)
white bishop on g2 attacks black pawn on d5 (directness: 2)
white queen on f3 attacks black pawn on d5 (directness: 1)

black knight on f6 defends black pawn on d5 (directness: 0)
black bishop on c6 defends black pawn on d5 (directness: 0)
black queen on d8 defends black pawn on d5 (directness: 0)

b: pawn 1
w: pawn 0
b: knight 3
w: knight 0
b: bishop 3
w: bishop 0
b: queen 9
(pawn, pawn, knight, knight, bishop, bishop, queen, 
|#

(: possibly-en-prise? (-> Piece (Listof Attack) (Listof Defense) Boolean))
(define (possibly-en-prise? piece attacks defenses)
  (let* ([balances (sequence-of-material-gain piece
                                              (sort-attacks-by-piece-value attacks)
                                              (sort-defenses-by-piece-value defenses)
                                              true
                                              0)]
         [len (length balances)])
    (or (exists-in (range len)
                   (lambda ([i : Integer])
                     (and (odd? i)
                          (> (list-ref balances i) 0))))
        (> (list-ref balances (- len 1)) 0))))

(define test1 (pos-from-fen "2bqk1br/r1pPppK1/3R1B2/PN1B4/p1RQ1n2/2p3P1/P1P2P1P/6N1 w k - 0 1"))
(define test2 (pos-from-fen "rn1qkbn1/pppppppN/2b5/3P1B2/4P3/3Q1B2/PPP1P1PP/RN2KB1R w KQq - 0 1"))
(define test3 (pos-from-fen "rn1qkbnr/ppp1pppp/2b5/3p4/4P3/5B2/PPPP1PQP/RNB1K1NR w KQkq - 0 1"))
(define test4 (pos-from-fen "r2qkb1r/ppp1pppp/2b2n2/3p4/1n2P3/2N2Q2/PPPP1PBP/RNB1K2R w KQkq - 0 1"))
(define test5 (pos-from-fen "rnb1kbnr/pp1p1ppp/2p1p3/3q4/8/1B3Q2/PPPPPPPP/RNB1K1NR w KQkq - 0 1"))

(define testpp (Position-pp test4))
(define attacks (attacks-of-pp testpp))  
;(displayln (attacks->string attacks))
(define defenses (defenses-of-pp testpp))
;(displayln (defenses->string defenses))
(define sorted-attacks (sort-attacks-by-target (Attacks-white attacks)))
(define sorted-defenses (sort-defenses-by-target (Defenses-black defenses)))
(define d5-attacks (sort-attacks-by-piece-value (hash-ref sorted-attacks (Square-location 4 3))))
(define d5-defenses (sort-defenses-by-piece-value (hash-ref sorted-defenses (Square-location 4 3))))
;(displayln (attack-list->string d5-attacks))
;(displayln (defense-list->string d5-defenses))
;(displayln (sorted-attacks->string sorted-attacks))
;(displayln (sorted-defenses->string sorted-defenses))
(displayln (sequence-of-material-gain 'pawn d5-attacks d5-defenses true 0))
(displayln (possibly-en-prise? 'pawn d5-attacks d5-defenses))

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

#|
(define positions-to-be-tested (list (list-ref positions 6)))
(define movesstrings-to-be-tested (list (list-ref movesstrings 6)))
(define indices-to-be-tested (list 7))

(perform-test positions-to-be-tested
              movesstrings-to-be-tested
              indices-to-be-tested)
|#
