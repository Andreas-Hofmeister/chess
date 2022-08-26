From CHESS Require Export legal_moves.
From CHESS Require Export basics.
From CHESS Require Export make_move.

Extract Inductive list => "list" [ "[]" "(::)" ].

Recursive Extraction CHESS.legal_moves.legal_moves CHESS.basics.initial_position CHESS.make_move.make_move.

