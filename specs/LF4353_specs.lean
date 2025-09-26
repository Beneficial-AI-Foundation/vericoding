-- <vc-preamble>
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
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bishop_diagonal (sq1 sq2 : Square) : List Square := sorry

theorem bishop_diagonal_output_format {sq1 sq2 : Square} :
  let result := bishop_diagonal sq1 sq2
  List.length result = 2 ∧ 
  (∀ sq ∈ result, sq.file ∈ chars ∧ sq.rank ∈ digits) ∧
  List.Pairwise (. ≤ .) result := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>