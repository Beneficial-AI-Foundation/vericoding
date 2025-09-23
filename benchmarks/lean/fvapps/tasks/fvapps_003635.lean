-- <vc-preamble>
def list_sum : List Nat → Nat
  | [] => 0
  | x::xs => x + list_sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def build_square (blocks: List Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_16_if_buildable {blocks : List Nat} :
  build_square blocks = true →
  list_sum blocks ≥ 16 :=
sorry

theorem input_unchanged {blocks : List Nat} :
  build_square blocks = b →
  blocks = blocks :=
sorry

theorem invalid_pieces {blocks : List Nat} :
  (∀ x ∈ blocks, x < 1 ∨ x > 4) →
  build_square blocks = false :=
sorry
-- </vc-theorems>