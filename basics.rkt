#lang typed/racket
(require racket/match)

(provide (all-defined-out))

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

(: piece-on-square (-> Square (Option Piece)))
(define (piece-on-square square)
  (match square
    ['empty-square 'none]
    [(Occupied-square c piece) (Some piece)]))

(define square-vector-set! (inst vector-set! Square))
(define square-vector-ref (inst vector-ref Square))
(define square-vector (inst vector Square))

(define-type File (Vectorof Square))

(: copy-file (-> File File))
(define (copy-file file)
  (match file
    [(vector s1 s2 s3 s4 s5 s6 s7 s8)
     (square-vector s1 s2 s3 s4 s5 s6 s7 s8)]))

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

(: copy-pp (-> Piece-placements Piece-placements))
(define (copy-pp pp)
  (match pp
    [(vector f1 f2 f3 f4 f5 f6 f7 f8)
     (file-vector (copy-file f1)
                  (copy-file f2)
                  (copy-file f3)
                  (copy-file f4)
                  (copy-file f5)
                  (copy-file f6)
                  (copy-file f7)
                  (copy-file f8))]))

(: file-indices (Listof Integer))
(define file-indices (list 0 1 2 3 4 5 6 7))
(: rank-indices (Listof Integer))
(define rank-indices (list 0 1 2 3 4 5 6 7))
(: indices-valid? (-> Integer Integer Boolean))
(define (indices-valid? rank file)
  (and (<= 0 rank) (<= rank 7) (<= 0 file) (<= file 7)))

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

(: piece->string (-> Piece String))
(define (piece->string p)
  (match p
    ['rook "r"]
    ['queen "q"]
    ['knight "n"]
    ['pawn "p"]
    ['king "k"]
    ['bishop "b"]))

(: square->output-string (-> Square String))
(define (square->output-string square)
  (match square
    ['empty-square "_"]
    [(Occupied-square 'black p) (piece->string p)]
    [(Occupied-square 'white p) (string-upcase (piece->string p))]))

(: rank->output-string (-> Rank String))
(define (rank->output-string rank)
  (let ([square-strings : (Listof String)
         (for/list ([i : Integer file-indices])
                 (square->output-string (get-square-of-rank rank i)))])
    (string-join square-strings "")))

(: pp->output-string (-> Piece-placements String))
(define (pp->output-string pp)
  (string-join
   (cons "  abcdefgh"
         (ann (for/list ([i (reverse rank-indices)])
                (string-append (number->string (+ 1 i)) " "
                               (rank->output-string (get-rank pp i))))
              (Listof String)))
   "\n" #:after-last "\n"))

(struct Square-location ([rank : Integer] [file : Integer]) #:transparent)

(: add-to-square-location (-> Square-location Integer Integer Square-location))
(define (add-to-square-location loc delta-x delta-y)
  (Square-location (+ (Square-location-rank loc) delta-y)
                   (+ (Square-location-file loc) delta-x)))

(: get-square-by-location (-> Piece-placements Square-location Square))
(define (get-square-by-location pp loc)
  (match loc
    [(Square-location rank file) (get-square pp rank file)]))

(: set-square-by-location! (-> Piece-placements Square-location Square Piece-placements))
(define (set-square-by-location! pp loc sq)
  (match loc
    [(Square-location rank file) (set-square! pp rank file sq)]))

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

(: locations-occupied-by-enemy-piece (-> Piece-placements (Listof Square-location) Color
                                         (Listof Square-location)))
(define (locations-occupied-by-enemy-piece pp locs c)
  (filter (lambda ([loc : Square-location]) (location-occupied-by-enemy-piece? pp loc c))
          locs))

(: occupied-by-friendly-piece? (-> Piece-placements Integer Integer Color Boolean))
(define (occupied-by-friendly-piece? pp rank file c)
  (match (get-square pp rank file)
    ['empty-square #f]
    [(Occupied-square occupied-color _) (if (equal? occupied-color c) #t #f)]))

(: location-occupied-by-friendly-piece? (-> Piece-placements Square-location Color Boolean))
(define (location-occupied-by-friendly-piece? pp loc c)
  (occupied-by-friendly-piece? pp (Square-location-rank loc) (Square-location-file loc) c))

(: locations-occupied-by-friendly-piece (-> Piece-placements (Listof Square-location) Color
                                         (Listof Square-location)))
(define (locations-occupied-by-friendly-piece pp locs c)
  (filter (lambda ([loc : Square-location]) (location-occupied-by-friendly-piece? pp loc c))
          locs))

(: locations-between (-> Square-location Square-location
                         (Listof Square-location)))
(define (locations-between from-location to-location)
  (: locations-along-direction (-> Square-location Integer Integer (Listof Square-location)))
  (define (locations-along-direction current-location dir-x dir-y)
    (if (equal? current-location to-location) '()
        (cons current-location
              (locations-along-direction
               (Square-location (+ dir-y (Square-location-rank current-location))
                                (+ dir-x (Square-location-file current-location)))
               dir-x dir-y))))
  (let* ([from-file (Square-location-file from-location)]
         [to-file (Square-location-file to-location)]
         [from-rank (Square-location-rank from-location)]
         [to-rank (Square-location-rank to-location)]
         [delta-x (- to-file from-file)]
         [delta-y (- to-rank from-rank)]
         [dir-x (sgn delta-x)]
         [dir-y (sgn delta-y)])
    (cond
      [(and (= 0 delta-x) (= 0 delta-y)) '()]
      [(or (= 0 delta-x) (= 0 delta-y) (= (abs delta-x) (abs delta-y)))
       (remove from-location
               (locations-along-direction from-location dir-x dir-y))]
      [else '()])))

(struct Pawn-double-step ([to-rank : Integer] [on-file : Integer]) #:transparent)

(define-type Castling-type (U 'queen-side 'king-side))

(struct Castling-availability ([castling-type : Castling-type] [color : Color]) #:transparent)

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

(: switch-to-move (-> Position Position))
(define (switch-to-move pos)
  (Position (Position-pp pos) (opponent-of (Position-to-move pos))
            'none (Position-castling-availabilities pos)))

(: make-initial-position (-> Position))
(define (make-initial-position)
  (Position (make-initial-pp) 'white 'none initial-castling-availabilities))

(: to-move->string (-> Color String))
(define (to-move->string c)
  (match c
    ['white "white to move"]
    ['black "black to move"]))

(: rank->string (-> Integer String))
(define (rank->string i)
  (format "~a" (+ i 1)))

(: file->string (-> Integer String))
(define (file->string i)
  (match i
    [0 "a"]
    [1 "b"]
    [2 "c"]
    [3 "d"]
    [4 "e"]
    [5 "f"]
    [6 "g"]
    [7 "h"]))

(: rank-file->string (-> Integer Integer String))
(define (rank-file->string rank file)
  (format "~a~a" (file->string file) (rank->string rank)))

(: square-location->string (-> Square-location String))
(define (square-location->string loc)
  (match loc
    [(Square-location rank file) (rank-file->string rank file)]))

(: string->file-index (-> String Integer))
(define (string->file-index s)
  (match s
    ["a" 0]
    ["b" 1]
    ["c" 2]
    ["d" 3]
    ["e" 4]
    ["f" 5]
    ["g" 6]
    ["h" 7]))

(: string->rank-index (-> String Integer))
(define (string->rank-index s)
  (match s
    ["1" 0]
    ["2" 1]
    ["3" 2]
    ["4" 3]
    ["5" 4]
    ["6" 5]
    ["7" 6]
    ["8" 7]))

(: string->square-location (-> String Square-location))
(define (string->square-location s)
  (Square-location (string->rank-index (substring s 0 1))
                   (string->file-index (substring s 1 2))))

(: pds->string (-> (Option Pawn-double-step) String))
(define (pds->string pds)
  (match pds
    ['none "the last move was not a pawn double step"]
    [(Some (Pawn-double-step on-file to-rank))
     (format "the last move was a pawn double step to ~a"
             (rank-file->string on-file to-rank))]))

(: castling-availability->string (-> Castling-availability String))
(define (castling-availability->string cavl)
  (match cavl
    [(Castling-availability type color)
     (format "~a->~a" color type)]))

(: castling-availabilities->string (-> (Listof Castling-availability) String))
(define (castling-availabilities->string cavls)
  (if (empty? cavls) "None"
      (string-join (map castling-availability->string cavls) ", ")))

(: pos->string (-> Position String))
(define (pos->string pos)
  (match pos
    [(Position pp to-move pds cavls) 
     (format "~a\n~a\ncastling availabilities: ~a\n~a"
             (to-move->string to-move)
             (pds->string pds)
             (castling-availabilities->string cavls)
             (pp->output-string pp))]))

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

(: find-piece (-> Piece-placements Color Piece (Listof Square-location) (Listof Square-location)))
(define (find-piece pp c p locs)
  (match locs
    ['() '()]
    [(cons (Square-location rank file) tl-locs)
     (if (equal? (get-square pp rank file)
                 (Occupied-square c p))
         (cons (Square-location rank file) (find-piece pp c p tl-locs))
         (find-piece pp c p tl-locs))]))

(: find-king (-> Piece-placements Color (Listof Square-location)))
(define (find-king pp c) (find-piece pp c 'king valid-locations))

