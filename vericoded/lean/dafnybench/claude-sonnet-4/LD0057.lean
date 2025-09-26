import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Convert Nat to Int safely
def natToInt (n : Nat) : Int := Int.ofNat n

-- LLM HELPER: Helper function to count elements satisfying a predicate
def countIf {α : Type*} (l : List α) (p : α → Bool) : Nat :=
  (l.filter p).length
-- </vc-helpers>

-- <vc-definitions>
def CountLessThan (numbers : List Int) (threshold : Int) : Int :=
natToInt (numbers.filter (fun i => decide (i < threshold))).length
-- </vc-definitions>

-- <vc-theorems>
theorem CountLessThan_spec (numbers : List Int) (threshold : Int) :
CountLessThan numbers threshold =
(numbers.filter (fun i => i < threshold)).length :=
by
  -- The proof follows from the definition
  simp only [CountLessThan, natToInt, Int.ofNat_inj]
  rfl
-- </vc-theorems>
