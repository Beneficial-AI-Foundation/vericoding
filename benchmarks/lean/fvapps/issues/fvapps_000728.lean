-- <vc-preamble>
def List.countElem (x : α) (xs : List α) [BEq α] : Nat :=
xs.filter (· == x) |>.length

def List.uniqueElems (xs : List α) [BEq α] : List α :=
xs.eraseDups
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def process_sequence (n : Nat) (arr : List Nat) : String × List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem process_sequence_valid_result (n : Nat) (arr : List Nat) :
  let (result, output) := process_sequence n arr
  (result = "YES" ∨ result = "NO") ∧ output.length ≥ 0 :=
sorry

theorem process_sequence_yes_properties (n : Nat) (arr : List Nat) 
  (h : arr.length > 0) (h2 : ∀ x ∈ arr, x > 0 ∧ x ≤ 1000) :
  let (result, output) := process_sequence n arr
  result = "YES" →
  -- Length properties
  output.length ≥ arr.uniqueElems.length ∧
  -- Maximum occurs once
  (let max := output.maximum?.getD 0
   output.countElem max = 1) ∧
  -- Each element occurs at most twice
  (∀ x ∈ output, output.countElem x ≤ 2) ∧
  -- First half unique
  (let firstHalf := output.take (arr.uniqueElems.length)
   firstHalf.uniqueElems.length = firstHalf.length) ∧
  -- Second half descending
  (let secondHalf := output.drop (arr.uniqueElems.length)
   ∀ i < secondHalf.length - 1,
     secondHalf[i]?.getD 0 ≥ secondHalf[i+1]?.getD 0) ∧
  -- Input elements preserved
  arr.uniqueElems.length = output.uniqueElems.length :=
sorry

theorem process_sequence_no_properties (n : Nat) (arr : List Nat)
  (h : arr.length > 0) (h2 : ∀ x ∈ arr, x > 0 ∧ x ≤ 1000) :
  let (result, output) := process_sequence n arr
  result = "NO" →
  output = [] ∧
  -- Any element occurs more than twice or max occurs more than once
  (∃ x ∈ arr, arr.countElem x > 2) ∨
  (let max := arr.maximum?.getD 0
   arr.countElem max > 1) :=
sorry
-- </vc-theorems>