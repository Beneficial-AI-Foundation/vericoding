-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.lower : String → String :=
  sorry

def String.swapcase : String → String :=
  sorry

def Char.swapcase : Char → Char :=
  sorry

def String.count (s₁ s₂ : String) : Nat :=
  sorry

def work_on_strings (s₁ s₂ : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem work_on_strings_length (a b : String) :
  (work_on_strings a b).length = a.length + b.length :=
sorry

theorem work_on_strings_substring_lengths (a b : String) :
  let result := work_on_strings a b
  (result.take a.length).length = a.length ∧
  (result.drop a.length).length = b.length :=
sorry

theorem work_on_strings_case_swap_first (a b : String) (i : String.Pos) :
  let result := work_on_strings a b
  let base := result.get i
  (b.lower.count (toString base).lower) % 2 = 1 →
  result = result.set i (base.swapcase) :=
sorry

theorem work_on_strings_case_swap_second (a b : String) (i : String.Pos) :
  let result := work_on_strings a b
  let base := result.get i
  (a.lower.count (toString base).lower) % 2 = 1 →
  result = result.set i (base.swapcase) :=
sorry

theorem work_on_strings_empty (s : String) :
  work_on_strings "" s = s ∧
  work_on_strings s "" = s ∧
  work_on_strings "" "" = "" :=
sorry

theorem work_on_strings_idempotent (s : String) :
  let result := work_on_strings s s
  work_on_strings s s = result :=
sorry
-- </vc-theorems>