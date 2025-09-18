-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rearrange_caps (nums: List Nat) : Option (List Nat) := sorry

theorem rearrange_caps_length {nums : List Nat} {result : List Nat} 
  (h : rearrange_caps nums = some result) : 
  result.length = nums.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rearrange_caps_different_positions {nums : List Nat} {result : List Nat}
  (h : rearrange_caps nums = some result) :
  ∀ (i : Fin nums.length), result.get ⟨i, by rw [rearrange_caps_length h]; exact i.2⟩ ≠ nums.get i := sorry

theorem rearrange_caps_same_elements {nums : List Nat} {result : List Nat}
  (h : rearrange_caps nums = some result) :
  ∀ x, List.countP (· = x) nums = List.countP (· = x) result := sorry

theorem rearrange_caps_none_if_majority {nums : List Nat} {n : Nat}
  (h : List.countP (· = n) nums > nums.length / 2) :
  rearrange_caps nums = none := sorry

theorem rearrange_caps_output_valid {nums : List Nat} {result : List Nat}
  (h : rearrange_caps nums = some result) :
  ∀ x, List.countP (· = x) nums = List.countP (· = x) result := sorry

theorem rearrange_caps_two_elems {a b : Nat} :
  rearrange_caps [a, b] = if a = b 
    then none
    else some [b, a] := sorry
-- </vc-theorems>