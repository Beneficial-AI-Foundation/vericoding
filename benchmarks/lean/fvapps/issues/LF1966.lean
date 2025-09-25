-- <vc-preamble>
def List.maximum (l : List Nat) : Nat :=
  sorry

def List.minimum (l : List Nat) : Nat :=
  sorry

def List.sum (l : List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_sweets (n m : Nat) (b g : List Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_inputs_return_negative_one (n m : Nat) (b g : List Nat)
  (h1 : n > 0) (h2 : m > 0)
  (h3 : b.length > 0) (h4 : g.length > 0) 
  (h5 : b.length ≤ 10) (h6 : g.length ≤ 10)
  (h7 : ∀ x ∈ b, x ≤ 100) (h8 : ∀ x ∈ g, x ≤ 100)
  (h9 : List.maximum b > List.minimum g) :
  min_sweets n m b g = -1 :=
sorry

theorem valid_inputs_result_nonnegative (n m g_len : Nat) (b g : List Nat)
  (h1 : n > 0) (h2 : m > 0) (h3 : g_len > 0)
  (h4 : n ≤ 10) (h5 : m ≤ 10) (h6 : g_len ≤ 10)
  (h7 : b.length = n)
  (h8 : g.length = g_len)
  (h9 : ∀ x ∈ b, x ≤ 100) (h10 : ∀ x ∈ g, x ≤ 100)
  (h11 : List.maximum b ≤ List.minimum g) :
  min_sweets n m b g ≥ 0 :=
sorry

theorem valid_inputs_result_exceeds_sum_girls (n m g_len : Nat) (b g : List Nat)
  (h1 : n > 0) (h2 : m > 0) (h3 : g_len > 0)
  (h4 : n ≤ 10) (h5 : m ≤ 10) (h6 : g_len ≤ 10)
  (h7 : b.length = n)
  (h8 : g.length = g_len)
  (h9 : ∀ x ∈ b, x ≤ 100) (h10 : ∀ x ∈ g, x ≤ 100)
  (h11 : List.maximum b ≤ List.minimum g) :
  min_sweets n m b g ≥ List.sum g :=
sorry

/-
info: 12
-/
-- #guard_msgs in
-- #eval min_sweets 3 2 [1, 2, 1] [3, 4]

/-
info: -1
-/
-- #guard_msgs in
-- #eval min_sweets 2 2 [0, 1] [1, 0]

/-
info: 4
-/
-- #guard_msgs in
-- #eval min_sweets 2 3 [1, 0] [1, 1, 2]
-- </vc-theorems>