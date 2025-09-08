/-
Given a list of white pawns on a chessboard (any number of them, meaning from 0 to 64 and with the possibility to be positioned everywhere), determine how many of them have their backs covered by another. 
Pawns attacking upwards since we have only white ones.

Please remember that a pawn attack(and defend as well) only the 2 square on the sides in front of him. https://en.wikipedia.org/wiki/Pawn_(chess)#/media/File:Pawn_(chess)_movements.gif

This is how the chess board coordinates are defined:
ABCDEFGH8♜♞♝♛♚♝♞♜7♟♟♟♟♟♟♟♟65432♙♙♙♙♙♙♙♙1♖♘♗♕♔♗♘♖
-/

-- <vc-helpers>
-- </vc-helpers>

def coveredPawns (pawns : List String) : Nat :=
  sorry

theorem covered_pawns_bounds {pawns : List String} :
  0 ≤ coveredPawns pawns ∧ coveredPawns pawns ≤ pawns.length :=
sorry

theorem covered_pawns_empty :
  coveredPawns [] = 0 :=
sorry

theorem covered_pawns_single (pawn : String) :
  coveredPawns [pawn] = 0 :=
sorry

theorem covered_pawns_adjacent {file rank : Char} (h1 : rank ≠ '1') 
  (h2 : file < 'h') :
  let pawn1 := String.mk [file, rank]
  let nextFile := Char.ofNat ((Char.toNat file) + 1)
  let prevRank := Char.ofNat ((Char.toNat rank) - 1)
  let pawn2 := String.mk [nextFile, prevRank]
  coveredPawns [pawn1, pawn2] = 1 :=
sorry

theorem covered_pawns_first_rank {file : Char} :
  coveredPawns [String.mk [file, '1']] = 0 :=
sorry 

theorem covered_pawns_edge_files {rank : Char} :
  (coveredPawns [String.mk ['a', rank]] = 0) ∧
  (coveredPawns [String.mk ['h', rank]] = 0) :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval covered_pawns ["f7", "b1", "h1", "c7", "h7"]

/-
info: 2
-/
-- #guard_msgs in
-- #eval covered_pawns ["e5", "b2", "b4", "g4", "a1", "a5"]

/-
info: 2
-/
-- #guard_msgs in
-- #eval covered_pawns ["a2", "b1", "c2"]

-- Apps difficulty: introductory
-- Assurance level: guarded