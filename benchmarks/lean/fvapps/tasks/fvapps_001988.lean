-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def transform_number (n : Nat) (a b : String) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem transform_number_valid_properties {n : Nat} {a b : String}
  (h1 : n ≥ 2) (h2 : n ≤ 10)
  (h3 : a.length = n) (h4 : b.length = n) 
  (h5 : ∀ c ∈ a.data, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'])
  (h6 : ∀ c ∈ b.data, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']) :
  let result := transform_number n a b
  (result = [(-1)] ∨ 
   (result = [] ∧ a = b) ∨
   (result.length ≥ 2 ∧ 
    ∀ move ∈ result.tail, 
      move < n ∧ 
      move.natAbs = 1)) :=
  sorry

theorem transform_number_identical {n : Nat} (h1 : n ≥ 2) (h2 : n ≤ 10) :
  transform_number n (String.mk (List.replicate n '5')) (String.mk (List.replicate n '5')) = [] :=
  sorry

theorem transform_number_bounds {n : Nat} {a : String}
  (h1 : n ≥ 2) (h2 : n ≤ 10) (h3 : a.length = n)
  (h4 : ∀ c ∈ a.data, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']) :
  let result := transform_number n a (String.mk (List.replicate n '9'))
  result = [(-1)] ∨ 
  (∀ x ∈ (List.map (λ c => c.toNat - '0'.toNat) a.data), 0 ≤ x ∧ x ≤ 9) :=
  sorry
-- </vc-theorems>