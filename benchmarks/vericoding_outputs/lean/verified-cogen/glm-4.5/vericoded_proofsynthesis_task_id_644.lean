import Mathlib
-- <vc-preamble>
@[reducible, simp]
def reverseToK_precond (list : Array Int) (n : Nat) : Prop :=
  list.size > 0 ∧ 0 < n ∧ n < list.size
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER Helper function to reverse a segment of an array
def reverseSegment (arr : Array α) (start len : Nat) : Array α :=
  if h : start + len ≤ arr.size then
    let front := arr.toList.take start
    let middle := (arr.toList.drop start).take len
    let back := arr.toList.drop (start + len)
    (front ++ middle.reverse ++ back).toArray
  else arr

-- LLM HELPER Lemma relating toArray and toList
lemma toList_toArray (l : List α) : l.toArray.toList = l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [ih]

-- LLM HELPER Lemma about take and drop
lemma take_append_drop (l : List α) (n : Nat) : l.take n ++ l.drop n = l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp [ih]
-- </vc-helpers>

-- <vc-definitions>
def reverseToK (list : Array Int) (n : Nat) (h_precond : reverseToK_precond list n) : Array Int :=
  ((list.toList.take n).reverse ++ (list.toList.drop n)).toArray
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def reverseToK_postcond (list : Array Int) (n : Nat) (result : Array Int) (h_precond : reverseToK_precond list n) : Prop :=
  result.toList = (list.toList.take n).reverse ++ (list.toList.drop n)

theorem reverseToK_spec_satisfied (list : Array Int) (n : Nat) (h_precond : reverseToK_precond list n) :
    reverseToK_postcond list n (reverseToK list n h_precond) h_precond := by
  unfold reverseToK_postcond reverseToK
  simp
-- </vc-theorems>

def main : IO Unit := 
  return ()