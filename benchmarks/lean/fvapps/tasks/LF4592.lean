-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def john (n : Nat) : List Nat :=
sorry

def ann (n : Nat) : List Nat :=
sorry

def sum_john (n : Nat) : Nat :=
sorry

def sum_ann (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sequences_start_correctly {n : Nat} (h : n > 0) :
  (john n).get ⟨0, sorry⟩ = 0 ∧ (ann n).get ⟨0, sorry⟩ = 1 :=
sorry

theorem sequence_lengths {n : Nat} (h : n > 0) :
  (john n).length = n ∧ (ann n).length = n :=
sorry

theorem sequences_nonnegative {n : Nat} (h : n > 0) :
  (∀ x ∈ john n, x ≥ 0) ∧ (∀ x ∈ ann n, x ≥ 0) :=
sorry

theorem sum_functions_match {n : Nat} (h : n > 0) :
  sum_john n = ((john n).foldl (· + ·) 0) ∧
  sum_ann n = ((ann n).foldl (· + ·) 0) :=
sorry

theorem sequence_relationship {n : Nat} (h : n > 0) :
  ∀ i : Nat, i < n → i > 0 →
    ((john n).get ⟨i, sorry⟩ = i - (ann n).get ⟨(john n).get ⟨i-1, sorry⟩, sorry⟩) ∧
    ((ann n).get ⟨i, sorry⟩ = i - (john n).get ⟨(ann n).get ⟨i-1, sorry⟩, sorry⟩) :=
sorry
-- </vc-theorems>