-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_connected_components (n : Nat) (numbers : List Nat) : Nat := sorry

theorem count_connected_components_properties (n : Nat) (numbers : List Nat) 
  (h1 : n > 0) (h2 : n ≤ 10) (h3 : numbers.length > 0)
  (h4 : ∀ x ∈ numbers, x < 2^n) :
  let result := count_connected_components n numbers;
  -- Result is natural number
  result > 0 
  ∧ result ≤ numbers.length
  -- Function is deterministic 
  ∧ result = count_connected_components n numbers
  -- Result invariant under reordering
  ∧ result = count_connected_components n numbers.reverse := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_number_gives_one_component (n : Nat) 
  (h1 : n > 0) (h2 : n ≤ 10) :
  let number := (2^n) - 1;
  count_connected_components n [number] = 1 := sorry
-- </vc-theorems>