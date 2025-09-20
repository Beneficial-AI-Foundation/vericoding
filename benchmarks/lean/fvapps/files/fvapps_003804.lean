-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def choose (n : Nat) (k : Nat) : Nat :=
  sorry

def counting_triangles (sticks : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem triangle_count_properties {sticks : List Nat}
  (h1 : sticks.length ≥ 3)
  (h2 : ∀ x ∈ sticks, x > 0 ∧ x ≤ 1000) :
  let result := counting_triangles sticks
  result ≥ 0 ∧ result ≤ choose sticks.length 3 :=
sorry

theorem same_lengths_make_triangles {n : Nat} (h : n > 0) :
  counting_triangles [n, n, n] = 1 :=
sorry

theorem triangle_inequality {sticks : List Nat}
  (h1 : sticks.length ≥ 3)
  (h2 : ∀ x ∈ sticks, x > 0 ∧ x ≤ 1000) :
  ∃ a b c, (a ∈ sticks ∧ b ∈ sticks ∧ c ∈ sticks) ∧
           (a + b > c → counting_triangles sticks > 0) :=
sorry

theorem order_invariance {sticks sticksSorted : List Nat}
  (h1 : sticks.length ≥ 3)
  (h2 : ∀ x ∈ sticks, x > 0 ∧ x ≤ 100)
  (h3 : ∀ x, (x ∈ sticks ↔ x ∈ sticksSorted)) :
  counting_triangles sticks = counting_triangles sticksSorted :=
sorry
-- </vc-theorems>