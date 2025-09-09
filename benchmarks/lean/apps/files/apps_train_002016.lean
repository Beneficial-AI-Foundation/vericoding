-- <vc-helpers>
-- </vc-helpers>

def count_pretty_substrings (s: String) : Nat :=
  sorry

theorem count_non_negative (s: String) : 
  count_pretty_substrings s ≥ 0 :=
  sorry

theorem count_bounded_by_length (s: String) :
  let n := s.length
  count_pretty_substrings s ≤ n * (n + 1) / 2 :=
  sorry 

theorem balanced_parens_pretty (n: Nat) :
  n > 0 → 
  let s := String.mk (List.replicate n '(' ++ List.replicate n ')')
  count_pretty_substrings s ≥ 1 := 
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_pretty_substrings "((?))"

/-
info: 7
-/
-- #guard_msgs in
-- #eval count_pretty_substrings "??()??"

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_pretty_substrings "??"

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible