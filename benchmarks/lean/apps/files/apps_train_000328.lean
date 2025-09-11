-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_complete_circuit (gas : List Nat) (cost : List Nat) : Int := sorry

theorem can_complete_circuit_valid_result {gas cost : List Nat} (h: gas.length > 0) (h2: cost.length > 0) :
  let result := can_complete_circuit gas cost
  result = -1 ∨ (0 ≤ result ∧ result < gas.length) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem insufficient_gas_implies_no_solution {gas cost : List Nat} (h: gas.length > 0) (h2: cost.length > 0) :
  (gas.foldl (· + ·) 0 < cost.foldl (· + ·) 0) →
  can_complete_circuit gas cost = -1 := sorry

theorem valid_result_implies_complete_circuit {gas cost : List Nat} (h: gas.length > 0) (h2: cost.length > 0) :
  let result := can_complete_circuit gas cost
  result ≠ -1 →
  ∀ i : Nat, i < gas.length →
  let tank := List.range i |>.foldl (fun acc j => 
    acc + gas[(result.toNat + j) % gas.length]! - cost[(result.toNat + j) % gas.length]!) 0
  tank ≥ 0 := sorry

theorem identical_gas_cost {values : List Nat} (h: values.length > 0) :
  can_complete_circuit values values = 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval can_complete_circuit [1, 2, 3, 4, 5] [3, 4, 5, 1, 2]

/-
info: -1
-/
-- #guard_msgs in
-- #eval can_complete_circuit [2, 3, 4] [3, 4, 3]

/-
info: 4
-/
-- #guard_msgs in
-- #eval can_complete_circuit [5, 1, 2, 3, 4] [4, 4, 1, 5, 1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded