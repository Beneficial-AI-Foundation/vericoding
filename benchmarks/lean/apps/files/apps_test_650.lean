-- <vc-preamble>
def ValidInput (word : String) : Prop :=
  1 ≤ word.length ∧ word.length ≤ 10 ∧ ∀ i : Nat, i < word.length → 'A' ≤ word.data[i]! ∧ word.data[i]! ≤ 'Z'

def Group1 : List Char := ['A','E','F','H','I','K','L','M','N','T','V','W','X','Y','Z']

def Group2 : List Char := ['B','C','D','G','J','O','P','Q','R','S','U']

def AllInGroup1 (word : String) : Prop :=
  ∀ i : Nat, i < word.length → word.data[i]! ∈ Group1

def AllInGroup2 (word : String) : Prop :=
  ∀ i : Nat, i < word.length → word.data[i]! ∈ Group2

def AllInSameGroup (word : String) : Prop :=
  AllInGroup1 word ∨ AllInGroup2 word

@[reducible, simp]
def solve_precond (word : String) : Prop :=
  ValidInput word
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (word : String) (h_precond : solve_precond word) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (word : String) (result : String) (h_precond : solve_precond word) : Prop :=
  (AllInSameGroup word ↔ result = "YES") ∧ (result = "YES" ∨ result = "NO")

theorem solve_spec_satisfied (word : String) (h_precond : solve_precond word) :
    solve_postcond word (solve word h_precond) h_precond := by
  sorry
-- </vc-theorems>