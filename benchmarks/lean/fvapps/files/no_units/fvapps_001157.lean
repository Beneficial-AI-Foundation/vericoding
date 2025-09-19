-- <vc-preamble>
def get_coins_and_sum (n: Nat) : List Nat × Nat :=
  sorry

def list_is_sorted {α: Type} (l: List α) (less_eq : α → α → Prop) : Prop :=
  ∀ i j, i < j → j < l.length → less_eq (l.get ⟨i, sorry⟩) (l.get ⟨j, sorry⟩)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_sum : List Nat → Nat 
  | [] => 0
  | x :: xs => x + list_sum xs
-- </vc-definitions>

-- <vc-theorems>
theorem coins_length_matches_input {n: Nat} (h: 1 ≤ n ∧ n ≤ 17):
  (get_coins_and_sum n).fst.length = n :=
sorry

theorem coins_are_positive {n: Nat} (h: 1 ≤ n ∧ n ≤ 17):
  ∀ x ∈ (get_coins_and_sum n).fst, 0 < x :=
sorry
-- </vc-theorems>