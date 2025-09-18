-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_modulo (arr : List Nat) : Nat := sorry 

@[simp] def max_list (l : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_modulo_non_negative (arr : List Nat) (h : arr.length > 0) :
  find_max_modulo arr ≥ 0 := sorry

theorem find_max_modulo_bounded_by_max (arr : List Nat) (h : arr.length > 0) :
  find_max_modulo arr ≤ max_list arr := sorry

theorem find_max_modulo_is_maximal (arr : List Nat) (h : arr.length > 0) :
  let max_val := max_list arr
  let others := arr.filter (· ≠ max_val)
  let second_max := if others.length > 0 then max_list others else 0
  let candidates := (arr.filter (· ≠ 0)).map (max_val % ·) ++ [second_max % max_val]
  find_max_modulo arr = max_list candidates := sorry

theorem find_max_modulo_duplicate_invariant (arr : List Nat) (h : arr.length > 0) :
  find_max_modulo arr = find_max_modulo (arr ++ arr) := sorry

theorem find_max_modulo_ordering_invariant {arr₁ arr₂ : List Nat} 
  (h₁ : arr₁.length > 0) (h₂ : arr₁.length = arr₂.length) 
  (h₃ : ∀ x, x ∈ arr₁ ↔ x ∈ arr₂) :
  find_max_modulo arr₁ = find_max_modulo arr₂ := sorry

theorem find_max_modulo_empty_error :
  ∀ (arr : List Nat), arr.length = 0 → find_max_modulo arr = 0 := sorry

theorem find_max_modulo_zero_error (arr : List Nat) :
  arr = [0] → find_max_modulo arr = 0 := sorry
-- </vc-theorems>