-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.rectangular (grid : List (List α)) : Bool :=
  sorry

def contains_cycle (grid : List (List Char)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem contains_cycle_empty_raises : ∀ (grid : List (List Char)),
  grid = [] ∨ grid.head?.map (λ row => row = []) = some true →
  contains_cycle grid = false :=
sorry

theorem contains_cycle_returns_bool : ∀ (grid : List (List Char)),
  grid ≠ [] →
  grid.head?.map (λ row => row ≠ []) = some true →
  grid.rectangular = true →
  (contains_cycle grid = true ∨ contains_cycle grid = false) :=
sorry

theorem contains_cycle_all_same_char : ∀ (c : Char) (n : Nat),
  n > 0 →
  let grid := List.replicate n (List.replicate n c);
  contains_cycle grid = (n > 1) :=
sorry

theorem contains_cycle_checkerboard : ∀ (n : Nat),
  n ≥ 2 →
  let grid := List.map (λ i => List.map (λ j => if (i+j)%2 = 0 then 'a' else 'b') (List.range n)) (List.range n);
  contains_cycle grid = false :=
sorry

theorem contains_cycle_border : ∀ (n : Nat),
  n ≥ 3 →
  let grid := List.map (λ i => List.map (λ j =>
    if i = 0 ∨ i = n-1 ∨ j = 0 ∨ j = n-1
    then 'a'
    else 'b') (List.range n)) (List.range n);
  contains_cycle grid = true :=
sorry
-- </vc-theorems>