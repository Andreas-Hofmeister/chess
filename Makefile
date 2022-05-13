all: basics.vo movement_basics.vo proof_tactics.v pawn_moves.vo \
rook_moves.vo bishop_moves.vo queen_moves.vo knight_moves.vo

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

clean:
	rm *.vo
