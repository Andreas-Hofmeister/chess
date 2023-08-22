#lang typed/racket
(require racket/match)

(require "basics.rkt")
(require "movement-basics.rkt")
(require "make-move.rkt")
(require "move-search.rkt")
(require "knight-moves.rkt")

(provide (all-defined-out))

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
         (let* ([new-attack (Attack attacker-loc piece color current-loc target-piece target-color current-directness)]
                [new-attacks (if (eq? color target-color) '() (list new-attack))])
           (if (hash-has-key? extension-pieces target-piece)
               (append new-attacks
                       (attacks-in-direction pp attacker-loc
                                             (add-to-square-location current-loc dir-x dir-y)
                                             (+ current-directness 1)
                                             color piece dir-x dir-y extension-pieces (min (- fuel 1)
                                                                                           (hash-ref extension-pieces target-piece))))
               new-attacks))])))

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

(: sort-attacks-by-attacker (-> (Listof Attack) 
                                (HashTable Square-location (Listof Attack))))
(define (sort-attacks-by-attacker attacks)
  (: sorted-attacks (HashTable Square-location (Listof Attack)))
  (define sorted-attacks (make-hash))
  (: iter (-> (Listof Attack) (HashTable Square-location (Listof Attack))))
  (define (iter remaining-attacks)
    (if (empty? remaining-attacks) sorted-attacks
        (let* ([attack (car remaining-attacks)]
               [attacker-loc (Attack-attacker-location attack)]
               [attacks-so-far : (Listof Attack) (hash-ref! sorted-attacks attacker-loc (lambda () '()))])
          (hash-set! sorted-attacks attacker-loc (cons attack attacks-so-far))
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

(: sort-defenses-by-defender (-> (Listof Defense) 
                                 (HashTable Square-location (Listof Defense))))
(define (sort-defenses-by-defender defenses)
  (: sorted-defenses (HashTable Square-location (Listof Defense)))
  (define sorted-defenses (make-hash))
  (: iter (-> (Listof Defense) (HashTable Square-location (Listof Defense))))
  (define (iter remaining-defenses)
    (if (empty? remaining-defenses) sorted-defenses
        (let* ([defense (car remaining-defenses)]
               [defender-loc (Defense-defender-location defense)]
               [defenses-so-far : (Listof Defense) (hash-ref! sorted-defenses defender-loc (lambda () '()))])
          (hash-set! sorted-defenses defender-loc (cons defense defenses-so-far))
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


(: sequence-of-material-gain (-> Piece (Listof Attack) (Listof Defense) Boolean Integer
                                 (Listof Integer)))
(define (sequence-of-material-gain target-piece sorted-attacks sorted-defenses attacker-to-move material-balance-so-far)
  (cond
    [(and attacker-to-move (empty? sorted-attacks)) '()]
    [(and (not attacker-to-move) (empty? sorted-defenses)) '()]
    [attacker-to-move
     (let* ([attack (car sorted-attacks)]
            [attacking-piece (Attack-attacker-piece attack)]
            [new-balance (+ material-balance-so-far (value-of-piece-for-en-prise target-piece))])
       (cons new-balance (sequence-of-material-gain attacking-piece
                                                    (cdr sorted-attacks)
                                                    sorted-defenses
                                                    false
                                                    new-balance)))]
    [else ; i.e. (not attacker-to-move)
     (let* ([defense (car sorted-defenses)]
            [defending-piece (Defense-defender-piece defense)]
            [new-balance (- material-balance-so-far (value-of-piece-for-en-prise target-piece))])
       (cons new-balance (sequence-of-material-gain defending-piece
                                                    sorted-attacks
                                                    (cdr sorted-defenses)
                                                    true
                                                    new-balance)))]))

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
        (and (> len 0)
             (> (list-ref balances (- len 1)) 0)))))

(: locations-with-possibly-en-prise-piece (-> Piece-placements
                                              (HashTable Square-location (Listof Attack))
                                              (HashTable Square-location (Listof Attack))
                                              (HashTable Square-location (Listof Defense))
                                              (HashTable Square-location (Listof Defense))                                             
                                              (Listof Square-location)))
(define (locations-with-possibly-en-prise-piece pp sorted-white-attacks sorted-black-attacks
                                                sorted-white-defenses sorted-black-defenses)
  (let* ([locations-en-prise : (Listof Square-location) '()])
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
            (when (possibly-en-prise? piece piece-attacks piece-defenses)
              (set! locations-en-prise (cons loc locations-en-prise))))]
         [_ 'nil]))
    locations-en-prise))

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

(: locations-with-equivalent-trades (-> Piece-placements
                                        (HashTable Square-location (Listof Attack))
                                        (HashTable Square-location (Listof Attack))
                                        (HashTable Square-location (Listof Defense))
                                        (HashTable Square-location (Listof Defense))
                                        (Listof Square-location)))
(define (locations-with-equivalent-trades pp sorted-white-attacks sorted-black-attacks
                                          sorted-white-defenses sorted-black-defenses)
  (let* ([locs : (Listof Square-location) '()])
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

(: value-of-piece-for-en-prise (-> Piece Integer))
(define (value-of-piece-for-en-prise p)
  (match p
    ['queen 9]
    ['rook 5]
    ['bishop 3]
    ['knight 3]
    ['pawn 1]
    ['king 700]))

(: piece< (-> Piece Piece Boolean))
(define (piece< piece1 piece2)
  (< (value-of-piece-for-en-prise piece1) (value-of-piece-for-en-prise piece2)))

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

