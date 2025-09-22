-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isRegular (s : String) : Bool :=
  sorry

def findRegularSubsequence (s : String) (k : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_regular_subsequence_properties
  (input : String)
  (k : Nat)
  (h1 : isRegular input = true)
  (h2 : k % 2 = 0)
  (h3 : k ≤ input.length)
  : let result := findRegularSubsequence input k
    (result.length = k) ∧
    (isRegular result = true) ∧
    (∀ c, c ∈ result.data → c = '(' ∨ c = ')') ∧
    (result.data.count '(' = result.data.count ')') ∧
    (∀ c, c ∈ result.data → c ∈ input.data) :=
sorry

theorem find_regular_subsequence_minimal_case :
  (findRegularSubsequence "()" 2 = "()") ∧
  (findRegularSubsequence "()" 0 = "") :=
sorry
-- </vc-theorems>