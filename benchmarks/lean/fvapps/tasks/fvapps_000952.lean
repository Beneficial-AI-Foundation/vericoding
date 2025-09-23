-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_horse_skill_diff (n : Nat) (skills : List Nat) : Nat :=
sorry

def list_max (l : List Nat) : Nat :=
sorry

def list_min (l : List Nat) : Nat :=
sorry

def list_sort (l : List Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_horse_skill_diff_nonneg {n : Nat} {skills : List Nat}
  (h : skills.length = n) (h2 : skills.length ≥ 2) :
  min_horse_skill_diff n skills ≥ 0 :=
sorry

theorem min_horse_skill_diff_le_range {n : Nat} {skills : List Nat}
  (h : skills.length = n) (h2 : skills.length ≥ 2) :
  min_horse_skill_diff n skills ≤ list_max skills - list_min skills :=
sorry

theorem min_horse_skill_diff_le_adjacent {n : Nat} {skills : List Nat} {i : Nat}
  (h : skills.length = n) (h2 : skills.length ≥ 2) (h3 : i < skills.length - 1) :
  min_horse_skill_diff n skills ≤
    (list_sort skills).get! (i+1) - (list_sort skills).get! i :=
sorry

theorem min_horse_skill_diff_order_inv {n : Nat} {skills shuffled : List Nat}
  (h : skills.length = n) (h2 : skills.length ≥ 2)
  (h3 : list_sort skills = list_sort shuffled) :
  min_horse_skill_diff n skills = min_horse_skill_diff n shuffled :=
sorry

theorem min_horse_skill_diff_invalid {n : Nat} {skills : List Nat}
  (h : skills.length ≠ n) :
  min_horse_skill_diff n skills = 0 :=
sorry
-- </vc-theorems>