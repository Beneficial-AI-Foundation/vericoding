-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.index {α} [BEq α] (xs : List α) (x : α) : Nat :=
  sorry

def check_subsequence (s1 : String) (s2 : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sequence_is_subsequence_of_itself (seq : List Nat) (h : seq.length > 0) :
  ∀ x ∈ seq, x > 0 ∧ x ≤ 100 →
  check_subsequence (toString seq) (toString seq) = "Yes" :=
sorry

theorem invalid_element_not_subsequence (seq : List Nat) (invalid : Nat) (h1 : seq.length > 0) :
  (∀ x ∈ seq, x > 0 ∧ x ≤ 100) →
  invalid > 100 ∧ invalid ≤ 200 →
  check_subsequence (toString seq) (toString invalid) = "No" :=
sorry

theorem first_element_is_subsequence (seq : List Nat) (h : seq.length > 1) :
  ∀ x ∈ seq, x > 0 ∧ x ≤ 100 →
  check_subsequence (toString seq) (toString (seq.get! 0)) = "Yes" :=
sorry

theorem consecutive_elements_subsequence (seq : List Nat) (start : Nat)
  (h1 : seq.length ≥ 3) (h2 : start < seq.length - 1) :
  ∀ x ∈ seq, x > 0 ∧ x ≤ 100 →
  let subseq := (seq.drop start).take 2
  ∀ i < subseq.length - 1,
    seq.index (subseq[i]!) < seq.index (subseq[i+1]!) →
  check_subsequence (toString seq) (toString subseq) = "Yes" :=
sorry
-- </vc-theorems>