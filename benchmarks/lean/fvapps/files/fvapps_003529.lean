-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def coveredPawns (pawns : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>