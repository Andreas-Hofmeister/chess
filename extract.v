From CHESS Require Export legal_moves.
From CHESS Require Export basics.
From CHESS Require Export make_move.
From CHESS Require Export move_search.


Extract Inductive list => "list" [ "[]" "(::)" ].

Recursive Extraction CHESS.legal_moves.legal_moves CHESS.basics.initial_position CHESS.make_move.make_move CHESS.move_search.evaluate_moves.

