-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumArrays (arrays : List (List Int)) (shift : Nat) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sumArrays_length {arrays : List (List Int)} {shift : Nat} 
  (h1 : arrays.length > 0)
  (h2 : ∀ (arr₁ arr₂ : List Int), arr₁ ∈ arrays → arr₂ ∈ arrays → arr₁.length = arr₂.length) :
  (sumArrays arrays shift).length = (arrays[0]!).length + shift * (arrays.length - 1) :=
  sorry

theorem sumArrays_zero_shift {arrays : List (List Int)} {shift : Nat}
  (h1 : arrays.length > 0)
  (h2 : ∀ (arr₁ arr₂ : List Int), arr₁ ∈ arrays → arr₂ ∈ arrays → arr₁.length = arr₂.length)
  (h3 : shift = 0) :
  sumArrays arrays shift = List.map (λ i => arrays.foldl (λ sum arr => sum + arr[0]!) 0) (List.range (arrays[0]!).length) :=
  sorry

theorem sumArrays_single_array {arr : List Int} {shift : Nat} :
  sumArrays [arr] shift = arr :=
  sorry

theorem sumArrays_element_bound {arrays : List (List Int)} {shift : Nat}
  (h1 : arrays.length > 0)
  (h2 : ∀ (arr₁ arr₂ : List Int), arr₁ ∈ arrays → arr₂ ∈ arrays → arr₁.length = arr₂.length) :
  ∀ (x : Int), x ∈ sumArrays arrays shift →
    x ≤ arrays.foldl (λ sum arr => sum + (arr.foldl (λ m x => max m x) 0)) 0 ∧
    -x ≤ arrays.foldl (λ sum arr => sum + (arr.foldl (λ m x => max m x) 0)) 0 :=
  sorry
-- </vc-theorems>