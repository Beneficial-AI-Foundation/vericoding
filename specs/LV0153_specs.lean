-- <vc-preamble>
@[reducible, simp]
def Match_precond (s : String) (p : String) : Prop :=
  s.toList.length = p.toList.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Match (s : String) (p : String) (h_precond : Match_precond (s) (p)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def Match_postcond (s : String) (p : String) (result: Bool) (h_precond : Match_precond (s) (p)) :=
  (result = true ↔ ∀ n : Nat, n < s.toList.length → ((s.toList[n]! = p.toList[n]!) ∨ (p.toList[n]! = '?')))

theorem Match_spec_satisfied (s: String) (p: String) (h_precond : Match_precond (s) (p)) :
    Match_postcond (s) (p) (Match (s) (p) h_precond) h_precond := by
  sorry
-- </vc-theorems>