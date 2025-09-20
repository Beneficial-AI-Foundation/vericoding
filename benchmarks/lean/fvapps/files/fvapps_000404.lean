-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_winner (arr : List Int) (k : Int) : Int :=
  sorry

def List.maximum (l : List Int) : Int :=
  sorry

def List.maximum' (l : List Int) (h : l ≠ []) : Int :=
  sorry

def List.findIndex (l : List Int) (p : Int → Bool) : Nat :=
  sorry

def List.sorted (l : List Int) (r : Int → Int → Bool) : Prop :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem winner_exists_in_array (arr : List Int) (h : arr ≠ []) :
  ∀ k, k > 0 → get_winner arr k ∈ arr :=
sorry
-- </vc-theorems>