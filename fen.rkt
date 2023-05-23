#lang typed/racket
(require racket/match)

(require "basics.rkt")

(provide (all-defined-out))

(: piece-chars (Listof Char))
(define piece-chars (string->list "kqrnbpKQRNBP"))
(: number-chars (Listof Char))
(define number-chars (string->list "1234567890"))
(: number-char->integer (-> Char Integer))
(define (number-char->integer c)
  (match c
    [#\1 1]
    [#\2 2]
    [#\3 3]
    [#\4 4]
    [#\5 5]
    [#\6 6]
    [#\7 7]
    [#\8 8]
    [#\9 9]
    [#\0 0]
    [else 0]))

(: char->square (-> Char Square))
(define (char->square c)
  (match c
    [#\k (Occupied-square 'black 'king)]
    [#\r (Occupied-square 'black 'rook)]
    [#\n (Occupied-square 'black 'knight)]
    [#\b (Occupied-square 'black 'bishop)]
    [#\q (Occupied-square 'black 'queen)]
    [#\p (Occupied-square 'black 'pawn)]
    [#\K (Occupied-square 'white 'king)]
    [#\R (Occupied-square 'white 'rook)]
    [#\N (Occupied-square 'white 'knight)]
    [#\B (Occupied-square 'white 'bishop)]
    [#\Q (Occupied-square 'white 'queen)]
    [#\P (Occupied-square 'white 'pawn)]))

(: pp-from-fen (-> String Piece-placements))
(define (pp-from-fen s)
  (: increment-file (-> Integer Integer Integer))
  (define (increment-file current-file delta)
    (let ([candidate (+ current-file delta)])
      (min candidate 7)))
  (: loop (-> Integer Integer String Piece-placements Piece-placements))
  (define (loop current-rank current-file rest-s pp-acc)
    (if (= (string-length rest-s) 0) pp-acc
        (let ([c (string-ref rest-s 0)])
          (cond
            [(set-member? piece-chars c)
             (begin (set-square! pp-acc current-rank current-file
                                 (char->square c))
                    (loop current-rank (increment-file current-file 1)
                          (substring rest-s 1) pp-acc))]
            [(equal? c #\/)
             (loop (- current-rank 1) 0 (substring rest-s 1) pp-acc)]
            [(set-member? number-chars c)
             (loop current-rank (increment-file current-file (number-char->integer c))
                   (substring rest-s 1) pp-acc)]
            [else pp-acc]))))
  (let ([empty-board (make-empty-board)])
    (loop 7 0 s empty-board)))

(: to-move-from-fen (-> String Color))
(define (to-move-from-fen s)
  (match s
    ["w" 'white]
    ["b" 'black]))

(: double-step-from-fen (-> String (Option Pawn-double-step)))
(define (double-step-from-fen s)
  (match s
    ["-" 'none]
    ["a3" (Some (Pawn-double-step 3 0))]
    ["b3" (Some (Pawn-double-step 3 1))]
    ["c3" (Some (Pawn-double-step 3 2))]
    ["d3" (Some (Pawn-double-step 3 3))]
    ["e3" (Some (Pawn-double-step 3 4))]
    ["f3" (Some (Pawn-double-step 3 5))]
    ["g3" (Some (Pawn-double-step 3 6))]
    ["h3" (Some (Pawn-double-step 3 7))]
    ["a6" (Some (Pawn-double-step 4 0))]
    ["b6" (Some (Pawn-double-step 4 1))]
    ["c6" (Some (Pawn-double-step 4 2))]
    ["d6" (Some (Pawn-double-step 4 3))]
    ["e6" (Some (Pawn-double-step 4 4))]
    ["f6" (Some (Pawn-double-step 4 5))]
    ["g6" (Some (Pawn-double-step 4 6))]
    ["h6" (Some (Pawn-double-step 4 7))]))

(: castling-availabilities-from-fen (-> String (Listof Castling-availability)))
(define (castling-availabilities-from-fen s)
  (: loop (-> (Listof Char) (Listof Castling-availability) (Listof Castling-availability)))
  (define (loop chars cavls-acc)
    (match chars
      ['() cavls-acc]
      [(cons #\K rest)
       (loop rest (cons (Castling-availability 'king-side 'white) cavls-acc))]
      [(cons #\Q rest)
       (loop rest (cons (Castling-availability 'queen-side 'white) cavls-acc))]
      [(cons #\k rest)
       (loop rest (cons (Castling-availability 'king-side 'black) cavls-acc))]
      [(cons #\q rest)
       (loop rest (cons (Castling-availability 'queen-side 'black) cavls-acc))]
      [(cons _ rest) (loop rest cavls-acc)]))
  (loop (string->list s) '()))

(: pos-from-fen (-> String Position))
(define (pos-from-fen s)
  (let* ([parts (string-split s)]
         [pp-s (list-ref parts 0)]
         [to-move-s (list-ref parts 1)]
         [castling-s (list-ref parts 2)]
         [double-step-s (list-ref parts 3)])
    (Position
     (pp-from-fen pp-s)
     (to-move-from-fen to-move-s)
     (double-step-from-fen double-step-s)
     (castling-availabilities-from-fen castling-s))))

(: piece-to-fen (-> Piece String))
(define (piece-to-fen p)
  (match p
    ['king "k"]
    ['queen "q"]
    ['rook "r"]
    ['bishop "b"]
    ['knight "n"]
    ['pawn "p"]))

(: square-to-fen (-> Square String))
(define (square-to-fen sq)
  (match sq
    [(Occupied-square 'white p) (string-upcase (piece-to-fen p))]
    [(Occupied-square 'black p) (piece-to-fen p)]
    ['empty-square "1"]))

(: fen-from-pp (-> Piece-placements String))
(define (fen-from-pp pp)
  (: fen-from-rank (-> Integer Integer Integer String String))
  (define (fen-from-rank rank-index file-index gap-acc fen-acc)
    (let ([sq (get-square pp rank-index file-index)])
      (cond
        [(and (equal? sq 'empty-square)
              (= file-index 7))
         (format "~a~a" fen-acc (+ gap-acc 1))]
        [(equal? sq 'empty-square)
         (fen-from-rank rank-index (+ file-index 1) (+ gap-acc 1) fen-acc)]
        [else
         (let* ([sq-fen (square-to-fen sq)]
                [gap-str (if (> gap-acc 0) (format "~a" gap-acc) "")]
                [new-fen (format "~a~a~a" fen-acc gap-str sq-fen)])
           (if (= file-index 7)
               (format "~a~a~a" fen-acc gap-str sq-fen)
               (fen-from-rank rank-index (+ file-index 1) 0 new-fen)))])))
  (string-join (map (lambda ([rank-index : Integer])
                      (fen-from-rank rank-index 0 0 ""))
                    (reverse rank-indices))
               "/"))

(: fen-from-color (-> Color String))
(define (fen-from-color c)
  (match c
    ['white "w"]
    ['black "b"]))

(: fen-from-castling-availability (-> Castling-availability String))
(define (fen-from-castling-availability cavl)
  (match cavl
    [(Castling-availability 'king-side 'white) "K"]
    [(Castling-availability 'queen-side 'white) "Q"]
    [(Castling-availability 'king-side 'black) "k"]
    [(Castling-availability 'queen-side 'black) "q"]))

(: fen-from-castling-availabilities (-> (Listof Castling-availability) String))
(define (fen-from-castling-availabilities cavls)
  (string-join (map fen-from-castling-availability cavls) ""))

(: fen-from-double-step (-> (Option Pawn-double-step) String))
(define (fen-from-double-step ds)
  (match ds
    ['none "-"]
    [(Some (Pawn-double-step 3 0)) "a3"]
    [(Some (Pawn-double-step 3 1)) "b3"]
    [(Some (Pawn-double-step 3 2)) "c3"]
    [(Some (Pawn-double-step 3 3)) "d3"]
    [(Some (Pawn-double-step 3 4)) "e3"]
    [(Some (Pawn-double-step 3 5)) "f3"]
    [(Some (Pawn-double-step 3 6)) "g3"]
    [(Some (Pawn-double-step 3 7)) "h3"]
    [(Some (Pawn-double-step 4 0)) "a6"]
    [(Some (Pawn-double-step 4 1)) "b6"]
    [(Some (Pawn-double-step 4 2)) "c6"]
    [(Some (Pawn-double-step 4 3)) "d6"]
    [(Some (Pawn-double-step 4 4)) "e6"]
    [(Some (Pawn-double-step 4 5)) "f6"]
    [(Some (Pawn-double-step 4 6)) "g6"]
    [(Some (Pawn-double-step 4 7)) "h6"]))

(: fen-from-position (-> Position String))
(define (fen-from-position pos)
  (string-join
   (list (fen-from-pp (Position-pp pos))
         (fen-from-color (Position-to-move pos))
         (fen-from-castling-availabilities (Position-castling-availabilities pos))
         (fen-from-double-step (Position-pawn-double-step pos))
         "0 1")
   " "))

(: fens-from-file (-> String (Listof String)))
(define (fens-from-file filepath)
  (file->lines filepath))

(: positions-from-file (-> String (Listof Position)))
(define (positions-from-file filepath)
  (map pos-from-fen (fens-from-file filepath)))

;(: fen1 String)
;(define fen1 "rnbqkbnr/pppppppp/8/8/8/8/pppppppp/RNBQKBNR w Kq e3 0 1")
;(display (pos->string (pos-from-fen fen1)))
;
;(display (fen-from-position (make-initial-position)))
;(display "\n")
