#lang typed/racket
(require racket/match)

(define-type Color (U 'black 'white))

(: opponent-of (-> Color Color))
(define (opponent-of c)
  (match c
    ['black 'white]
    ['white 'black]))

(define-type Piece (U 'pawn 'king 'queen 'rook 'bishop 'knight))

(struct occupied-square ([c : Color] [p : Piece]))
(define-type Square (U 'empty-square occupied-square))

(define-type File (Vectorof Square))
(define-type Piece-placements (Vectorof File))

(: make-empty-file (-> File))
(define (make-empty-file)
  (make-vector 8 'empty-square))

(define make-file (inst vector Square))

(define make-file-vector (inst vector File))

(: make-pp (-> (Listof File) Piece-placements))
(define (make-pp files)
  (apply make-file-vector files))

(: make-empty-board (-> Piece-placements))
(define (make-empty-board)
  (let ([list-of-empty-files : (Listof File)
         (for/list ([i '(0 1 2 3 4 5 6 7)])
           (make-empty-file))])
    (make-pp list-of-empty-files)))

(: initial-file-with-piece (-> Piece File))
(define (initial-file-with-piece p)
  (make-file
   (occupied-square 'white p)
   (occupied-square 'white 'pawn)
   'empty-square
   'empty-square
   'empty-square
   'empty-square
   (occupied-square 'black 'pawn)
   (occupied-square 'black p)))

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

(define file-vector-set! (inst vector-set! Square))
(define board-vector-ref (inst vector-ref (Vectorof Square)))
