-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.get_thue_morse_seq (n : Nat) : List Nat := sorry
def is_thue_morse (seq : List Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_sequence_length (n : Nat) (h : n > 0) :
  is_thue_morse (List.get_thue_morse_seq n) := sorry

theorem invalid_sequences (seq : List Nat) (h₁ : seq.length > 0) (h₂ : ∀ x ∈ seq, x = 0 ∨ x = 1) :
  seq ≠ List.get_thue_morse_seq seq.length → ¬is_thue_morse seq := sorry

theorem sequence_starts_with_zero (n : Nat) (h : n > 0) :
  (List.get_thue_morse_seq n).head? = some 0 := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_thue_morse [0, 1, 1, 0, 1]

/-
info: True
-/
-- #guard_msgs in
-- #eval is_thue_morse [0]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_thue_morse [1]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded