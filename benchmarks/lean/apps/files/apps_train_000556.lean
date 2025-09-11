-- <vc-preamble>
def reduce_recipe (ingredients : List Nat) : List Nat := sorry

def gcd (a b : Nat) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcdl (l : List Nat) : Nat := sorry

theorem reduce_recipe_proportions (ingredients : List Nat)
  (h : ∀ x ∈ ingredients, x > 0) :
  let result := reduce_recipe ingredients
  ∀ i j, i < ingredients.length → j < ingredients.length →
    ingredients[i]! * result[j]! = ingredients[j]! * result[i]! := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reduce_recipe_gcd (ingredients : List Nat)
  (h : ∀ x ∈ ingredients, x > 0) :
  gcdl (reduce_recipe ingredients) = 1 := sorry

theorem gcd_divides (a b : Nat) (h₁ : a > 0) (h₂ : b > 0) :
  let g := gcd a b
  g ∣ a ∧ g ∣ b := sorry

theorem gcd_commutative (a b : Nat) (h₁ : a > 0) (h₂ : b > 0) :
  gcd a b = gcd b a := sorry

theorem reduce_recipe_nat (ingredients : List Nat)
  (h : ∀ x ∈ ingredients, x > 0) :
  ∀ x, x ∈ reduce_recipe ingredients → x > 0 := sorry

/-
info: [1, 1]
-/
-- #guard_msgs in
-- #eval reduce_recipe [4, 4]

/-
info: [2, 3, 4]
-/
-- #guard_msgs in
-- #eval reduce_recipe [2, 3, 4]

/-
info: [1, 5, 3, 2]
-/
-- #guard_msgs in
-- #eval reduce_recipe [3, 15, 9, 6]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded