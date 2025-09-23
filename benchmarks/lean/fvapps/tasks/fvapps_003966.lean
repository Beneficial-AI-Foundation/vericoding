-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def greatest_distance (lst: List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem greatest_distance_nonnegative (lst: List Int) : 
  greatest_distance lst ≥ 0 :=
sorry

theorem greatest_distance_duplicate_lower_bound {lst : List Int} {i j : Nat} : 
  i < j → j < lst.length → 
  (h1 : i < lst.length) → (h2 : j < lst.length) →
  lst.get ⟨i, h1⟩ = lst.get ⟨j, h2⟩ → 
  greatest_distance lst ≥ j - i :=
sorry

theorem greatest_distance_unique_list {lst : List Int} : 
  lst.Nodup → greatest_distance lst = 0 :=
sorry

theorem greatest_distance_repeated_element (x : Int) :
  greatest_distance [x, x, x] = 2 :=
sorry
-- </vc-theorems>