-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validate_word (s : String) : Bool := sorry

theorem permutations_invariant (s₁ s₂ : String) : 
  Perm s₁.toList s₂.toList → validate_word s₁ = validate_word s₂ := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem repeat_string_equiv (s : String) (n : Nat) :
  n > 0 → validate_word (String.join (List.replicate n s)) = validate_word s := sorry 

theorem single_char_string_valid (c : Char) (n : Nat) :
  n > 0 → validate_word (String.mk (List.replicate n c)) = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval validate_word "abcabc"

/-
info: True
-/
-- #guard_msgs in
-- #eval validate_word "AbcCBa"

/-
info: False
-/
-- #guard_msgs in
-- #eval validate_word "abcabcd"
-- </vc-theorems>