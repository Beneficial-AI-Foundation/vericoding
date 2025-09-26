import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-
Utility alias for the filtered count used by CountLessThan.
Not strictly necessary, but can help future proofs.
-/
def countLT (numbers : List Int) (threshold : Int) : Nat :=
  (numbers.filter (fun i => i < threshold)).length

@[simp] lemma countLT_def (numbers : List Int) (threshold : Int) :
    countLT numbers threshold = (numbers.filter (fun i => i < threshold)).length := rfl
-- </vc-helpers>

-- <vc-definitions>
def CountLessThan (numbers : List Int) (threshold : Int) : Int :=
Int.ofNat ((numbers.filter (fun i => i < threshold)).length)
-- </vc-definitions>

-- <vc-theorems>
theorem CountLessThan_spec (numbers : List Int) (threshold : Int) :
CountLessThan numbers threshold =
(numbers.filter (fun i => i < threshold)).length :=
by
  rfl
-- </vc-theorems>
