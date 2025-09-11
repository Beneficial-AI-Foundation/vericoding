-- <vc-preamble>
def is_prime (n : Nat) : Bool := sorry

def all_dig_prime (n : Nat) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def not_primes (start finish : Nat) : List Nat := sorry

def List.sorted (l : List Nat) : Prop := 
  ∀ i j, i < j → j < l.length → 
  match l.get? i, l.get? j with
  | some x, some y => x ≤ y
  | _, _ => true
-- </vc-definitions>

-- <vc-theorems>
theorem not_primes_empty_for_equal_bounds (n : Nat) :
  not_primes n n = [] := sorry

theorem not_primes_empty_for_invalid_range (start finish : Nat)
  (h : finish < start) :
  not_primes start finish = [] := sorry

/-
info: [22, 25, 27, 32, 33, 35, 52, 55, 57, 72, 75]
-/
-- #guard_msgs in
-- #eval not_primes 2 77

/-
info: [522, 525, 527, 532, 533, 535, 537, 552, 553, 555, 572, 573, 575]
-/
-- #guard_msgs in
-- #eval not_primes 500 600

/-
info: [2722, 2723, 2725, 2727, 2732, 2733, 2735, 2737]
-/
-- #guard_msgs in
-- #eval not_primes 2700 2750
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible