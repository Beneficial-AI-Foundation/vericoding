-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_sequence (n : Nat) (arr : List Int) : String := sorry

theorem check_sequence_returns_valid_output (n : Nat) (arr : List Int) :
  n > 0 → arr.length > 0 →
  (check_sequence n arr = "prekrasnyy" ∨ check_sequence n arr = "ne krasivo") :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_sequence_prekrasnyy_implies_unique (n : Nat) (arr : List Int) :
  n > 0 → arr.length > 0 →
  check_sequence n arr = "prekrasnyy" →
  ∀ (i : Fin arr.length) (j : Fin arr.length), 
    i.val ≠ j.val → (arr.get i) ≠ (arr.get j) :=
sorry

theorem check_sequence_ne_krasivo_implies_duplicate (n : Nat) (arr : List Int) :
  n > 0 → arr.length > 0 →
  check_sequence n arr = "ne krasivo" →
  ∃ (i : Fin arr.length) (j : Fin arr.length), 
    i.val ≠ j.val ∧ (arr.get i) = (arr.get j) :=
sorry

theorem check_sequence_n_independent (n₁ n₂ : Nat) (arr : List Int) :
  n₁ > 0 → n₂ > 0 → arr.length > 0 →
  check_sequence n₁ arr = check_sequence n₂ arr :=
sorry

theorem check_sequence_single_element (n : Nat) (arr : List Int) :
  n > 0 → arr.length = 1 →
  check_sequence n arr = "prekrasnyy" :=
sorry
-- </vc-theorems>