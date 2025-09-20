-- <vc-preamble>
def getPairs (l: List Nat) : List (Nat × Nat) :=
  match l with
  | [] => []
  | x :: xs => (xs.map (fun y => (x, y))) ++ getPairs xs

def abs (n: Nat) (m: Nat) : Nat :=
  if n ≥ m then n - m else m - n

def pairSum (pairs: List (Nat × Nat)) : Nat :=
  match pairs with
  | [] => 0
  | (x, y) :: rest => abs x y + pairSum rest
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_ad_revenue (n: Nat) (team_strengths: List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem revenue_nonnegative (n: Nat) (team_strengths: List Nat)
  (h1: n ≥ 2) (h2: team_strengths.length = n) :
  calculate_ad_revenue n team_strengths ≥ 0 :=
sorry

theorem revenue_matches_manual_calc (n: Nat) (team_strengths: List Nat)
  (h1: n ≥ 2) (h2: team_strengths.length = n) :
  calculate_ad_revenue n team_strengths = pairSum (getPairs team_strengths) :=
sorry

theorem revenue_pair_count (n: Nat) (team_strengths: List Nat)
  (h1: n ≥ 2) (h2: team_strengths.length = n) :
  (getPairs team_strengths).length = n * (n-1) / 2 :=
sorry

theorem identical_strengths_zero_revenue (n: Nat) (x: Nat)
  (h1: n ≥ 2) :
  calculate_ad_revenue n (List.replicate n x) = 0 :=
sorry

theorem minimal_cases :
  calculate_ad_revenue 2 [0, 0] = 0 ∧
  calculate_ad_revenue 2 [0, 1] = 1 :=
sorry
-- </vc-theorems>