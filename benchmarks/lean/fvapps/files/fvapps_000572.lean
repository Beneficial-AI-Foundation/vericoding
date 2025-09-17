-- <vc-preamble>
def abs (x : Int) : Int :=
  if x ≥ 0 then x else -x

def gcd (a b : Int) : Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minPizzaCuts (n : Nat) (angles : List Nat) : Nat :=
  sorry

-- GCD theorems
-- </vc-definitions>

-- <vc-theorems>
theorem gcd_positive {a b : Int} (h : a ≠ 0 ∨ b ≠ 0) : 
  gcd (abs a) (abs b) > 0 :=
  sorry

theorem gcd_divides {a b : Int} : 
  let d := gcd (abs a) (abs b)
  (a ≠ 0 → abs a % d = 0) ∧ 
  (b ≠ 0 → abs b % d = 0) :=
  sorry

-- Pizza cuts theorems

theorem minPizzaCuts_nonnegative {n : Nat} {angles : List Nat} :
  minPizzaCuts n angles ≥ 0 :=
  sorry

theorem minPizzaCuts_upper_bound {n : Nat} {angles : List Nat} 
  (h : List.length angles = n) :
  minPizzaCuts n angles + n ≤ 360 :=
  sorry

theorem minPizzaCuts_rotation_invariant {n : Nat} {angles : List Nat}
  (h : List.length angles = n) :
  minPizzaCuts n angles = 
  minPizzaCuts n (List.map (fun x => (x + 45) % 360) angles) :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_pizza_cuts 4 [0, 90, 180, 270]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_pizza_cuts 2 [90, 210]

/-
info: 358
-/
-- #guard_msgs in
-- #eval min_pizza_cuts 2 [0, 1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded