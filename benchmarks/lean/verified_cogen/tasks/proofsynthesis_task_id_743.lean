-- <vc-preamble>
-- Specification function for rotation split point
def rotationSplit (len : Nat) (n : Nat) : Int :=
  len - (n % len)

-- Precondition for rotate_right function
@[reducible, simp]
def rotateRight_precond (list : Array UInt32) (n : Nat) : Prop :=
  list.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rotateRight (list : Array UInt32) (n : Nat) (h_precond : rotateRight_precond list n) : Array UInt32 :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def rotateRight_postcond (list : Array UInt32) (n : Nat) (newList : Array UInt32) (h_precond : rotateRight_precond list n) : Prop :=
  newList.size = list.size ∧ 
  newList.toList = (list.toList.drop (rotationSplit list.size n).natAbs) ++ (list.toList.take (rotationSplit list.size n).natAbs)

theorem rotateRight_spec_satisfied (list : Array UInt32) (n : Nat) (h_precond : rotateRight_precond list n) :
    rotateRight_postcond list n (rotateRight list n h_precond) h_precond := by
  sorry
-- </vc-theorems>