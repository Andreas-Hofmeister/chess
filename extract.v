From CHESS Require Export legal_moves.

Extract Inductive list => "list" [ "[]" "(::)" ].

Recursive Extraction CHESS.legal_moves.legal_moves.
