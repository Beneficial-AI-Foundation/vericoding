-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_killers (n : Nat) (reports : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_report_one (n : Nat) (h : n ≥ 2) :
  let reports := (List.replicate n 1).set 0 0
  let result := find_killers n reports
  ∀ i, i ∈ result ↔ (2 ≤ i ∧ i ≤ n) :=
sorry

theorem chain_structure (n : Nat) (h : n ≥ 2) :
  let reports := 0 :: List.range (n-1)
  let result := find_killers n reports
  n ∈ result :=
sorry
-- </vc-theorems>