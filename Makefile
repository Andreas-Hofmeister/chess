all: basics.vo movement_basics.vo proof_tactics.v pawn_moves.vo \
rook_moves.vo bishop_moves.vo queen_moves.vo knight_moves.vo king_moves.vo \
attacks.vo check.vo castling.vo make_move.vo legal_moves.vo engine.ml uci

basics.vo: basics.v proof_tactics.vo
	coqc -Q . CHESS basics.v

movement_basics.vo: movement_basics.v basics.vo proof_tactics.vo
	coqc -Q . CHESS movement_basics.v

proof_tactics.vo: proof_tactics.v
	coqc -Q . CHESS proof_tactics.v

pawn_moves.vo: pawn_moves.v basics.vo movement_basics.vo \
proof_tactics.vo
	coqc -Q . CHESS pawn_moves.v

rook_moves.vo: rook_moves.v basics.vo movement_basics.vo \
proof_tactics.vo
	coqc -Q . CHESS rook_moves.v

bishop_moves.vo: bishop_moves.v basics.vo movement_basics.vo \
proof_tactics.vo
	coqc -Q . CHESS bishop_moves.v

queen_moves.vo: queen_moves.v basics.vo movement_basics.vo \
proof_tactics.vo bishop_moves.vo rook_moves.vo
	coqc -Q . CHESS queen_moves.v

knight_moves.vo: knight_moves.v basics.vo movement_basics.vo \
proof_tactics.vo
	coqc -Q . CHESS knight_moves.v

king_moves.vo: king_moves.v basics.vo movement_basics.vo \
proof_tactics.vo
	coqc -Q . CHESS king_moves.v

attacks.vo: movement_basics.vo pawn_moves.vo rook_moves.vo \
bishop_moves.vo knight_moves.vo queen_moves.vo king_moves.vo attacks.v
	coqc -Q . CHESS attacks.v

check.vo: attacks.vo check.v
	coqc -Q . CHESS check.v

castling.vo: check.vo attacks.vo castling.v
	coqc -Q . CHESS castling.v

make_move.vo: basics.vo movement_basics.vo make_move.v
	coqc -Q . CHESS make_move.v

legal_moves.vo: make_move.vo attacks.vo legal_moves.v
	coqc -Q . CHESS legal_moves.v

engine.ml: legal_moves.vo extract.v
	coqc -Q . CHESS extract.v > engine.ml
	
uci: uci.ml engine.ml
	ocamlopt -o uci engine.ml uci.ml

clean:
	rm *.vo engine.ml uci
