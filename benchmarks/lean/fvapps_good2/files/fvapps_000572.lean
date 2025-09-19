-- <vc-preamble>
def abs (x : Int) : Int :=
  if x ≥ 0 then x else -x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcd (a b : Int) : Int :=
  sorry

def minPizzaCuts (n : Nat) (angles : List Nat) : Nat :=
  sorry
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
-- </vc-theorems>