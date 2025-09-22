-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isUniform (s : String) : String :=
  sorry

def countTransitions (s : String) : Nat :=
  sorry

def reverseString (s : String) : String :=
  sorry

def swapBits (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem uniform_string_result_valid {s : String} (h : s.length > 0) :
  isUniform s = "uniform" ∨ isUniform s = "non-uniform" :=
sorry

theorem all_same_chars_uniform {s : String} (h₁ : s.length > 0)
  (h₂ : ∀ (i j : String.Pos), s.get i = s.get j) :
  isUniform s = "uniform" :=
sorry

theorem transitions_gt_two_nonuniform {s : String} (h₁ : s.length > 0)
  (h₂ : countTransitions s > 2) :
  isUniform s = "non-uniform" :=
sorry

theorem transitions_leq_two_uniform {s : String} (h₁ : s.length > 0)
  (h₂ : countTransitions s ≤ 2) :
  isUniform s = "uniform" :=
sorry

theorem uniform_reverse_eq {s : String} (h : s.length > 0) :
  isUniform s = isUniform (reverseString s) :=
sorry

theorem uniform_swap_eq {s : String} (h : s.length > 0) :
  isUniform s = isUniform (swapBits s) :=
sorry
-- </vc-theorems>