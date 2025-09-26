-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_in_array {α : Type} [Inhabited α] (arr : List α) (pred : α → Nat → Bool) : Int := sorry

theorem find_specific_value {α : Type} [Inhabited α] [BEq α] (arr : List α) (target : α) :
  let result := find_in_array arr (fun x _ => x == target)
  result ≠ -1 → (result.toNat < arr.length ∧ arr[result.toNat]! = target) ∧
  result = -1 → ∀ x ∈ arr, x ≠ target := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_at_index {α : Type} [Inhabited α] (arr : List α) (index : Nat) :
  let result := find_in_array arr (fun _ i => i == index)
  result ≠ -1 → result.toNat = index ∧
  result = -1 → index ≥ arr.length := sorry

theorem first_match_returned {α : Type} [Inhabited α] (arr : List α) :
  let result := find_in_array arr (fun _ _ => true)
  (arr.length > 0 → result = 0) ∧
  (arr.length = 0 → result = -1) := sorry

theorem no_match_returns_negative {α : Type} [Inhabited α] (arr : List α) :
  find_in_array arr (fun _ _ => false) = -1 := sorry

theorem index_matches_value [Inhabited Int] (arr : List Int) :
  let result := find_in_array arr (fun x i => x.toNat = i)
  result ≠ -1 → arr[result.toNat]!.toNat = result.toNat ∧
  result = -1 → ∀ (i : Nat), i < arr.length → arr[i]!.toNat ≠ i := sorry
-- </vc-theorems>