-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def odd_one (arr : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem odd_one_returns_valid_index_or_minus_one (arr : List Int) :
  let result := odd_one arr
  (result = -1 → ∀ x ∈ arr, x % 2 = 0) ∧ 
  (result ≠ -1 → 
    result ≥ 0 ∧ 
    result < arr.length ∧
    (let val := arr.get? (result.toNat); match val with
    | some x => x % 2 = 1 ∨ x % 2 = -1
    | none => False) ∧
    ∀ i, i < result → 
      let val := arr.get? (i.toNat); match val with
      | some x => x % 2 = 0
      | none => True) :=
  sorry

theorem all_even_returns_minus_one (arr : List Int) :
  (∀ x ∈ arr, x % 2 = 0) → odd_one arr = -1 :=
  sorry

theorem all_odd_returns_first_index (arr : List Int) :
  arr ≠ [] →
  (∀ x ∈ arr, x % 2 = 1) → 
  odd_one arr = 0 :=
  sorry
-- </vc-theorems>