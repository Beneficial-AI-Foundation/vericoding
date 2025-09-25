-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_carousel_coloring (n : Nat) (types : List Nat) : CarouselResult :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem color_count_valid {n : Nat} {types : List Nat}
  (h1 : n > 0) (h2 : types.length = n) :
  let result := solve_carousel_coloring n types
  result.colorCount ≤ 3 ∧ 
  ∀ c ∈ result.colors, 1 ≤ c ∧ c ≤ result.colorCount := 
  sorry

theorem output_length {n : Nat} {types : List Nat} 
  (h1 : n > 0) (h2 : types.length = n) :
  (solve_carousel_coloring n types).colors.length = n :=
  sorry

theorem same_type_same_color {n : Nat} {types : List Nat}
  (h1 : n > 0) (h2 : types.length = n)
  (h3 : ∀ i j, i < types.length → j < types.length → types[i]! = types[j]!) :
  let result := solve_carousel_coloring n types
  result.colorCount = 1 ∧ 
  ∀ c ∈ result.colors, c = 1 :=
  sorry

theorem even_length_alternating {n : Nat}
  (h1 : n > 1) (h2 : n % 2 = 0) :
  let types := List.join (List.replicate (n/2) [1,2])
  let result := solve_carousel_coloring n types
  result.colorCount = 2 ∧ result.colors.length = n :=
  sorry

/-
info: n1
-/
-- #guard_msgs in
-- #eval len colors1

/-
info: n2
-/
-- #guard_msgs in
-- #eval len colors2
-- </vc-theorems>