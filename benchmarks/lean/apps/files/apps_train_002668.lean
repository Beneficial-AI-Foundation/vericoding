-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def productFib (n : Nat) : (Nat × Nat × Bool) := sorry

def fib : Nat → Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem product_fib_valid_structure 
  (n : Nat) 
  (h : n ≤ 10^8) :
  let (a, b, bool) := productFib n
  a ≥ 0 ∧ b ≥ a := sorry

theorem product_fib_consecutive_fibs
  (n : Nat)
  (h : n ≤ 10^8) :
  let (a, b, _) := productFib n
  ∃ k, fib k = a ∧ fib (k + 1) = b := sorry

theorem product_fib_boolean_correctness
  (n : Nat)
  (h : n ≤ 10^8) :
  let (a, b, isExact) := productFib n
  (isExact → a * b = n) ∧ 
  (¬isExact → a * b > n) ∧
  (¬isExact → ∃ k, fib k = a ∧ fib (k-1) * fib k < n) := sorry

/-
info: [21, 34, True]
-/
-- #guard_msgs in
-- #eval productFib 714

/-
info: [34, 55, False]
-/
-- #guard_msgs in
-- #eval productFib 800

/-
info: [0, 1, True]
-/
-- #guard_msgs in
-- #eval productFib 0
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded