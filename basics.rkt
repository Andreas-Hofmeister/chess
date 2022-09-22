#lang typed/racket
(require racket/match)

(struct (a) Some ([v : a]))
(define-type (Option a) (U 'none (Some a)))

(define-type Color (U 'black 'white))

(: opponent-of (-> Color Color))
(define (opponent-of c)
  (match c
    ['black 'white]
    ['white 'black]))

(define-type Piece (U 'pawn 'king 'queen 'rook 'bishop 'knight))

(struct Occupied-square ([c : Color] [p : Piece]) #:transparent)
(define-type Square (U 'empty-square Occupied-square))

(define square-vector-set! (inst vector-set! Square))
(define square-vector-ref (inst vector-ref Square))
(define square-vector (inst vector Square))

(define-type File (Vectorof Square))

(: make-file (-> (Listof Square) File))
(define (make-file squares)
  (apply square-vector squares))

(: make-empty-file (-> File))
(define (make-empty-file)
  (make-vector 8 'empty-square))

(: get-square-of-file (-> File Integer Square))
(define (get-square-of-file file i)
  (square-vector-ref file i))

(define file-vector (inst vector File))

(define-type Rank (Vectorof Square))

(: get-square-of-rank (-> Rank Integer Square))
(define (get-square-of-rank rank i)
  (square-vector-ref rank i))

(: make-rank (-> (Listof Square) Rank))
(define (make-rank squares)
  (apply square-vector squares))

(define-type Piece-placements (Vectorof File))

(: file-indices (Listof Integer))
(define file-indices (list 0 1 2 3 4 5 6 7))
(: rank-indices (Listof Integer))
(define rank-indices (list 0 1 2 3 4 5 6 7))

(define pp-vector-ref (inst vector-ref File))

(: make-pp (-> (Listof File) Piece-placements))
(define (make-pp files)
  (apply file-vector files))

(: make-empty-board (-> Piece-placements))
(define (make-empty-board)
  (let ([list-of-empty-files : (Listof File)
         (for/list ([i : Integer file-indices])
           (make-empty-file))])
    (make-pp list-of-empty-files)))

(: initial-file-with-piece (-> Piece File))
(define (initial-file-with-piece p)
  (make-file
   (list
    (Occupied-square 'white p)
    (Occupied-square 'white 'pawn)
    'empty-square
    'empty-square
    'empty-square
    'empty-square
    (Occupied-square 'black 'pawn)
    (Occupied-square 'black p))))

(define (initial-file-a) (initial-file-with-piece 'rook))
(define (initial-file-b) (initial-file-with-piece 'knight))
(define (initial-file-c) (initial-file-with-piece 'bishop))
(define (initial-file-d) (initial-file-with-piece 'queen))
(define (initial-file-e) (initial-file-with-piece 'king))
(define (initial-file-f) (initial-file-with-piece 'bishop))
(define (initial-file-g) (initial-file-with-piece 'knight))
(define (initial-file-h) (initial-file-with-piece 'rook))

(: make-initial-pp (-> Piece-placements))
(define (make-initial-pp)
  (make-pp (list (initial-file-a) (initial-file-b) (initial-file-c) (initial-file-d)
             (initial-file-e) (initial-file-f) (initial-file-g) (initial-file-h))))

(: get-file (-> Piece-placements Integer File))
(define (get-file pp i)
  (pp-vector-ref pp i))

(: get-files (-> Piece-placements (Listof File)))
(define (get-files pp)
  (for/list ([file-index : Integer file-indices])
    (get-file pp file-index)))

(: get-rank (-> Piece-placements Integer Rank))
(define (get-rank pp i)
  (make-rank (map (lambda ([file : File]) (get-square-of-file file i))
                  (get-files pp))))

(: get-square (-> Piece-placements Integer Integer Square))
(define (get-square pp rank-index file-index)
  (get-square-of-file (get-file pp file-index) rank-index))

(: set-square! (-> Piece-placements Integer Integer Square Piece-placements))
(define (set-square! pp rank-index file-index square)
  (square-vector-set! (get-file pp file-index) rank-index square)
  pp)

(: piece-to-str (-> Piece String))
(define (piece-to-str p)
  (match p
    ['rook "r"]
    ['queen "q"]
    ['knight "n"]
    ['pawn "p"]
    ['king "k"]
    ['bishop "b"]))

(: square-to-str (-> Square String))
(define (square-to-str square)
  (match square
    ['empty-square "_"]
    [(Occupied-square 'black p) (piece-to-str p)]
    [(Occupied-square 'white p) (string-upcase (piece-to-str p))]))

(: rank-to-str (-> Rank String))
(define (rank-to-str rank)
  (let ([square-strings : (Listof String)
         (for/list ([i : Integer file-indices])
                 (square-to-str (get-square-of-rank rank i)))])
    (string-join square-strings "")))

(: pp-to-str (-> Piece-placements String))
(define (pp-to-str pp)
  (string-join
   (cons "  abcdefgh"
         (ann (for/list ([i (reverse rank-indices)])
                (string-append (number->string (+ 1 i)) " "
                               (rank-to-str (get-rank pp i))))
              (Listof String)))
   "\n" #:after-last "\n"))

(struct Square-location ([rank : Integer] [file : Integer]) #:transparent)

(: get-square-by-location (-> Piece-placements Square-location Square))
(define (get-square-by-location pp loc)
  (match loc
    [(Square-location rank file) (get-square pp rank file)]))

(: square-empty-rank-file? (-> Piece-placements Integer Integer Boolean))
(define (square-empty-rank-file? pp rank file)
  (match (get-square pp rank file)
    ['empty-square #t]
    [_ #f]))

(: square-empty? (-> Piece-placements Square-location Boolean))
(define (square-empty? pp loc)
  (match loc
    [(Square-location rank file) (square-empty-rank-file? pp rank file)]))

(: occupied-by-enemy-piece? (-> Piece-placements Integer Integer Color Boolean))
(define (occupied-by-enemy-piece? pp rank file c)
  (match (get-square pp rank file)
    ['empty-square #f]
    [(Occupied-square occupied-color _) (if (equal? occupied-color c) #f #t)]))

(: location-occupied-by-enemy-piece? (-> Piece-placements Square-location Color Boolean))
(define (location-occupied-by-enemy-piece? pp loc c)
  (occupied-by-enemy-piece? pp (Square-location-rank loc) (Square-location-file loc) c))

(struct Pawn-double-step ([to-rank : Integer] [on-file : Integer]) #:transparent)

(define-type Castling-type (U 'queen-side 'king-side))

(struct Castling-availability ([castling-type : Castling-type] [c : Color]) #:transparent)

(define initial-castling-availabilities
  (list (Castling-availability 'queen-side 'white)
        (Castling-availability 'king-side 'white)
        (Castling-availability 'queen-side 'black)
        (Castling-availability 'king-side 'black)))

(struct Position ([pp : Piece-placements]
                  [to-move : Color]
                  [pawn-double-step : (Option Pawn-double-step)]
                  [castling-availabilities : (Listof Castling-availability)])
  #:transparent)

(: make-initial-position (-> Position))
(define (make-initial-position)
  (Position (make-initial-pp) 'white 'none initial-castling-availabilities))

(: difference (-> Integer Integer Integer))
(define (difference i j)
  (abs (- i j)))

(: squares-adjacent? (-> Square-location Square-location Boolean))
(define (squares-adjacent? loc1 loc2)
  (let ([rank1 (Square-location-rank loc1)]
        [file1 (Square-location-file loc1)]
        [rank2 (Square-location-rank loc2)]
        [file2 (Square-location-file loc2)])
    (and (not (equal? loc1 loc2))
         (<= (difference rank1 rank2) 1)
         (<= (difference file1 file2) 1))))

(: location-valid? (-> Square-location Boolean))
(define (location-valid? loc)
  (let ([rank (Square-location-rank loc)]
        [file (Square-location-file loc)])
    (and (<= 0 rank) (<= rank 7)
         (<= 0 file) (<= file 7))))

(: valid-locations (Listof Square-location))
(define valid-locations
  (for*/list: : (Listof Square-location)
    ([i : Integer rank-indices]
     [j : Integer file-indices])
    (Square-location i j)))
   
(: adjacent-squares (-> Square-location (Listof Square-location)))
(define (adjacent-squares loc)
  (let ([rank (Square-location-rank loc)]
        [file (Square-location-file loc)])
    (filter (lambda (adj-loc) (location-valid? adj-loc))
            (list (Square-location rank (+ 1 file))
                  (Square-location (+ 1 rank) (+ 1 file))
                  (Square-location (+ 1 rank) file)
                  (Square-location (+ 1 rank) (- file 1))
                  (Square-location rank (- file 1))
                  (Square-location (- rank 1) (- file 1))
                  (Square-location (- rank 1) file)
                  (Square-location (- rank 1) (+ file 1))))))

(: exists-in (All (a) (-> (Listof a) (-> a Boolean) Boolean)))
(define (exists-in l cond-f)
  (match l
    ['() #f]
    [(cons hd tl) (if (cond-f hd) #t (exists-in tl cond-f))]))

(: forall-in (All (a) (-> (Listof a) (-> a Boolean) Boolean)))
(define (forall-in l cond-f)
  (match l
    ['() #t]
    [(cons hd tl) (if (not (cond-f hd)) #f (forall-in tl cond-f))]))

(: find-piece (-> Position Color Piece (Listof Square-location) (Listof Square-location)))
(define (find-piece pos c p locs)
  (match locs
    ['() '()]
    [(cons (Square-location rank file) tl-locs)
     (if (equal? (get-square (Position-pp pos) rank file)
                 (Occupied-square c p))
         (cons (Square-location rank file) (find-piece pos c p tl-locs))
         (find-piece pos c p tl-locs))]))

(: find-king (-> Position Color (Listof Square-location)))
(define (find-king pos c) (find-piece pos c 'king valid-locations))

