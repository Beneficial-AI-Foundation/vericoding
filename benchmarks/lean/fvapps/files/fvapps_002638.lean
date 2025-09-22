-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hofstadter_Q : Nat → Nat 
| 0 => 0
| n => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hofstadter_positive (n : Nat) (h : n > 0) : 
  hofstadter_Q n > 0 := sorry

theorem hofstadter_first_terms : 
  hofstadter_Q 1 = 1 ∧ hofstadter_Q 2 = 1 := sorry

theorem hofstadter_recurrence (n : Nat) (h : n ≥ 3) :
  hofstadter_Q n = 
    hofstadter_Q (n - hofstadter_Q (n-1)) + 
    hofstadter_Q (n - hofstadter_Q (n-2)) := sorry

theorem hofstadter_deterministic (n : Nat) (h : n > 0) :
  ∀ x y, hofstadter_Q n = x → hofstadter_Q n = y → x = y := sorry
-- </vc-theorems>