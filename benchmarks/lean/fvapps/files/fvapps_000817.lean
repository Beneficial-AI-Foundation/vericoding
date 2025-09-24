-- <vc-preamble>
def enumerate_add (shops : List Nat) : List Nat :=
  let range := List.range shops.length
  List.map (fun i => shops[i]! + i) range
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_list (l : List Nat) : Nat := sorry

def find_min_velocity (n : Nat) (shops : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_velocity_greater_than_max_attractiveness (n : Nat) (shops : List Nat)
  (h : shops.length > 0) :
  find_min_velocity n shops ≥ max_list shops :=
sorry

theorem min_velocity_accounts_for_position (n : Nat) (shops : List Nat) (pos : Nat)
  (h1 : pos < shops.length) (h2 : shops.length > 0) :
  find_min_velocity n shops ≥ shops[pos]! + pos :=
sorry

theorem min_velocity_allows_decreasing_speeds (n : Nat) (shops : List Nat)
  (h : shops.length ≥ 2) :
  ∀ i : Nat, i < shops.length →
  find_min_velocity n shops - i ≥ shops[i]! :=
sorry

theorem min_velocity_is_optimal (n : Nat) (shops : List Nat)
  (h : shops.length > 0) :
  find_min_velocity n shops = max_list (enumerate_add shops) :=
sorry
-- </vc-theorems>