def chars := ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h']
def digits := ['1', '2', '3', '4', '5', '6', '7', '8']

structure Square where
  file : Char
  rank : Char
  h_file : file ∈ chars
  h_rank : rank ∈ digits

instance : Ord Square where
  compare a b := 
    match compare a.file b.file with
    | .eq => compare a.rank b.rank
    | c => c

instance : LE Square where
  le a b := compare a b ≠ .gt

-- <vc-helpers>
-- </vc-helpers>

def bishop_diagonal (sq1 sq2 : Square) : List Square := sorry

theorem bishop_diagonal_output_format {sq1 sq2 : Square} :
  let result := bishop_diagonal sq1 sq2
  List.length result = 2 ∧ 
  (∀ sq ∈ result, sq.file ∈ chars ∧ sq.rank ∈ digits) ∧
  List.Pairwise (. ≤ .) result := sorry

theorem bishop_diagonal_same_square {sq : Square} :
  bishop_diagonal sq sq = [sq, sq] := sorry 

theorem bishop_diagonal_symmetry {sq1 sq2 : Square} :
  bishop_diagonal sq1 sq2 = bishop_diagonal sq2 sq1 := sorry

theorem bishop_diagonal_bounds {sq1 sq2 : Square} :
  let result := bishop_diagonal sq1 sq2
  ∀ sq ∈ result, 
    0 ≤ (Char.toNat sq.file - Char.toNat 'a') ∧ 
    (Char.toNat sq.file - Char.toNat 'a') ≤ 7 ∧
    0 ≤ (Char.toNat sq.rank - Char.toNat '1') ∧
    (Char.toNat sq.rank - Char.toNat '1') ≤ 7 := sorry

/-
info: ['c8', 'h3']
-/
-- #guard_msgs in
-- #eval bishop_diagonal "d7" "f5"

/-
info: ['b5', 'd8']
-/
-- #guard_msgs in
-- #eval bishop_diagonal "d8" "b5"

/-
info: ['a1', 'h8']
-/
-- #guard_msgs in
-- #eval bishop_diagonal "a1" "h8"

-- Apps difficulty: introductory
-- Assurance level: unguarded