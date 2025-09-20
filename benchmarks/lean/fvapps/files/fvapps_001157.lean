-- <vc-preamble>
def list_is_sorted {α: Type} (l: List α) (less_eq : α → α → Prop) : Prop :=
  ∀ i j (h1 : i < j) (h2 : j < l.length), less_eq (l.get ⟨i, Nat.lt_trans h1 h2⟩) (l.get ⟨j, h2⟩)

def list_sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + list_sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_coins_and_sum (n: Nat) : List Nat × Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem coins_length_matches_input {n: Nat} (h: 1 ≤ n ∧ n ≤ 17):
  (get_coins_and_sum n).fst.length = n :=
sorry

theorem coins_are_positive {n: Nat} (h: 1 ≤ n ∧ n ≤ 17):
  ∀ x ∈ (get_coins_and_sum n).fst, 0 < x :=
sorry
-- </vc-theorems>