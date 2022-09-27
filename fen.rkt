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

(: fen1 String)
(define fen1 "rnbqkbnr/pppppppp/8/8/8/8/pppppppp/RNBQKBNR")
(display (pp->string (pp-from-fen fen1)))
