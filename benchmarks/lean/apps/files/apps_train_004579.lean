-- <vc-helpers>
-- </vc-helpers>

def mutate (chromosome : List Char) (p : Float) : List Char := sorry

theorem mutate_preserves_length (chromosome : List Char) (p : Float) 
  (h1 : 0 ≤ p) (h2 : p ≤ 1) :
  (mutate chromosome p).length = chromosome.length := sorry

theorem mutate_valid_bits (chromosome : List Char) (p : Float)
  (h1 : 0 ≤ p) (h2 : p ≤ 1)
  (h3 : ∀ c, c ∈ chromosome → c = '0' ∨ c = '1') :
  ∀ c, c ∈ (mutate chromosome p) → c = '0' ∨ c = '1' := sorry

theorem mutate_zero_prob (chromosome : List Char) :
  mutate chromosome 0 = chromosome := sorry

theorem mutate_one_prob (chromosome : List Char)
  (h : ∀ c, c ∈ chromosome → c = '0' ∨ c = '1') :
  ∀ (c₁ : Char) (c₂ : Char), 
    c₁ ∈ chromosome → 
    c₂ ∈ (mutate chromosome 1) →
    c₁ ≠ c₂ := sorry

theorem mutate_deterministic (chromosome : List Char) (p : Float)
  (h1 : 0 ≤ p) (h2 : p ≤ 1) :
  mutate chromosome p = mutate chromosome p := sorry

/-
info: '0'
-/
-- #guard_msgs in
-- #eval mutate "0" 0

/-
info: '1'
-/
-- #guard_msgs in
-- #eval mutate "0" 1

/-
info: len(test)
-/
-- #guard_msgs in
-- #eval len mutate(test, 0.3)

-- Apps difficulty: introductory
-- Assurance level: unguarded