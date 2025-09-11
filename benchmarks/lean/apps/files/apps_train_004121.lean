-- <vc-preamble>
def hidden (n : Nat) : String := sorry

theorem hidden_length_matches_input {n : Nat} :
  (toString n).length = (hidden n).length := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hidden_withInt (n : Int) : String := sorry

theorem hidden_rejects_negative (n : Int) :
  n < 0 → hidden_withInt n = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hidden_valid_chars {n : Nat} {c : Char} :
  c ∈ (hidden n).data → c ∈ ['o', 'b', 'l', 'i', 'e', 'a', 't', 'd', 'n', 'm'] := sorry

theorem hidden_consistent_mapping {n₁ n₂ : Nat} {i : Nat} {pos1 : String.Pos} {pos2 : String.Pos} :
  i < min (toString n₁).length (toString n₂).length →
  (toString n₁).get pos1 = (toString n₂).get pos2 →
  (hidden n₁).get pos1 = (hidden n₂).get pos2 := sorry

/-
info: 'aid'
-/
-- #guard_msgs in
-- #eval hidden 637

/-
info: 'dean'
-/
-- #guard_msgs in
-- #eval hidden 7468

/-
info: 'email'
-/
-- #guard_msgs in
-- #eval hidden 49632
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded