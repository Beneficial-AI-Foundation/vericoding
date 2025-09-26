import Mathlib
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
noncomputable section
open Classical

-- LLM HELPER
lemma ite_yes_no_cases (p : Prop) [Decidable p] :
    ((if p then "YES" else "NO") = "YES" ∨ (if p then "YES" else "NO") = "NO") := by
  by_cases p <;> simp [*]

-- </vc-helpers>

-- <vc-definitions>
def solve (word : String) (h_precond : solve_precond word) : String :=
  if AllInSameGroup word then "YES" else "NO"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (word : String) (result : String) (h_precond : solve_precond word) : Prop :=
  (AllInSameGroup word ↔ result = "YES") ∧ (result = "YES" ∨ result = "NO")

theorem solve_spec_satisfied (word : String) (h_precond : solve_precond word) :
    solve_postcond word (solve word h_precond) h_precond := by
  
  classical
  have h1 : (AllInSameGroup word ↔ solve word h_precond = "YES") := by
    by_cases hgrp : AllInSameGroup word <;> simp [solve, hgrp]
  have h2 : (solve word h_precond = "YES" ∨ solve word h_precond = "NO") := by
    have hcases := ite_yes_no_cases (AllInSameGroup word)
    simpa [solve] using hcases
  simpa [solve_postcond] using And.intro h1 h2
end
-- </vc-theorems>
