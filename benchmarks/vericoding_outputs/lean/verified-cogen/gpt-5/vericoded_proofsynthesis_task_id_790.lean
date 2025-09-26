import Mathlib
-- <vc-preamble>
@[reducible, simp]
def isEvenAtEvenIndex_precond (arr : Array Nat) := True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No additional helpers needed for this verification task.
-- </vc-helpers>

-- <vc-definitions>
def isEvenAtEvenIndex (arr : Array Nat) (h_precond : isEvenAtEvenIndex_precond (arr)) : Bool :=
  by
  classical
  exact if ∀ i, i < arr.size → ((i % 2) = (arr[i]! % 2)) then true else false
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isEvenAtEvenIndex_postcond (arr : Array Nat) (result: Bool) (h_precond : isEvenAtEvenIndex_precond (arr)) :=
  (∀ i, i < arr.size → ((i % 2) = (arr[i]! % 2))) ↔ result

theorem isEvenAtEvenIndex_spec_satisfied (arr: Array Nat) (h_precond : isEvenAtEvenIndex_precond (arr)) :
    isEvenAtEvenIndex_postcond (arr) (isEvenAtEvenIndex (arr) h_precond) h_precond := by
  classical
unfold isEvenAtEvenIndex_postcond
by_cases hP : ∀ i, i < arr.size → ((i % 2) = (arr[i]! % 2))
·
  have hgoal : (∀ i, i < arr.size → ((i % 2) = (arr[i]! % 2))) ↔ True :=
    Iff.intro (fun _ => True.intro) (fun _ => hP)
  simpa [isEvenAtEvenIndex, hP] using hgoal
·
  have hgoal : (∀ i, i < arr.size → ((i % 2) = (arr[i]! % 2))) ↔ False :=
    Iff.intro (fun hp => (hP hp).elim) (fun hFalse => False.elim hFalse)
  simpa [isEvenAtEvenIndex, hP] using hgoal
-- </vc-theorems>
