-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def controller (s : String) : String := sorry

theorem controller_output_length (s : String) :
  (controller s).length = s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem controller_output_digits (s : String) :
  ∀ c ∈ (controller s).data, c = '0' ∨ c = '1' ∨ c = '2' ∨ c = '3' ∨ c = '4' ∨ c = '5' := sorry

theorem controller_sequential_moves (s : String) :
  ∀ i, i > 0 → i < (controller s).length → 
    let nums := (controller s).data.map (fun c => c.toNat - '0'.toNat);
    nums[i]! ≤ nums[i-1]! + 1 ∧ nums[i-1]! ≤ nums[i]! + 1 := sorry

theorem controller_boundaries (s : String) :
  ∀ c ∈ (controller s).data, 
    '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '5'.toNat := sorry

theorem controller_stops_at_limits (s : String) :
  ∀ i, i > 0 → i < (controller s).length - 1 →
    let nums := (controller s).data.map (fun c => c.toNat - '0'.toNat);
    (nums[i]! = 0 ∧ nums[i+1]! ≠ nums[i]! → nums[i+1]! > nums[i]!) ∧
    (nums[i]! = 5 ∧ nums[i+1]! ≠ nums[i]! → nums[i+1]! < nums[i]!) := sorry
-- </vc-theorems>