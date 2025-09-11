-- <vc-preamble>
def coprimes (n : Nat) : List Nat := sorry

def gcd (a b : Nat) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countCoprimes (n : Nat) : Nat :=
  (List.range n).filter (fun x => gcd x n = 1) |>.length
-- </vc-definitions>

-- <vc-theorems>
theorem coprimes_all_less (n : Nat) (h : n ≥ 2) :
  ∀ x ∈ coprimes n, x > 0 ∧ x < n := sorry

/-
info: [1]
-/
-- #guard_msgs in
-- #eval coprimes 2

/-
info: [1, 2]
-/
-- #guard_msgs in
-- #eval coprimes 3

/-
info: [1, 3, 7, 9]
-/
-- #guard_msgs in
-- #eval coprimes 10
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible