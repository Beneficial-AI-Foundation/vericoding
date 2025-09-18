-- <vc-preamble>
def penalty (nums : List Nat) : String := sorry

def stringIsAllDigits (s : String) : Bool := 
  s.all Char.isDigit
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def listToSortedString (l : List Nat) : String := 
  let strList := l.map toString
  String.join strList
-- </vc-definitions>

-- <vc-theorems>
theorem penalty_output_is_numeric (nums : List Nat) (h : nums ≠ []) : 
  let result := penalty nums
  stringIsAllDigits result = true := sorry

theorem penalty_preserves_digits (nums : List Nat) (h : nums ≠ []) :
  let input_digits := String.join (List.map toString nums)
  let result := penalty nums
  input_digits.length = result.length := sorry 

theorem penalty_single_digits (nums : List Nat) (h₁ : nums ≠ []) 
  (h₂ : ∀ n ∈ nums, n ≤ 9) :
  penalty nums = listToSortedString nums := sorry

theorem penalty_self_consistent (nums₁ nums₂ : List Nat) 
  (h₁ : nums₁ ≠ []) (h₂ : nums₂ ≠ [])
  (h₃ : nums₁ = nums₂) :
  penalty nums₁ = penalty nums₂ := sorry

/-
info: '1304550'
-/
-- #guard_msgs in
-- #eval penalty ["45", "30", "50", "1"]

/-
info: '100101'
-/
-- #guard_msgs in
-- #eval penalty ["100", "10", "1"]

/-
info: '323'
-/
-- #guard_msgs in
-- #eval penalty ["32", "3"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded