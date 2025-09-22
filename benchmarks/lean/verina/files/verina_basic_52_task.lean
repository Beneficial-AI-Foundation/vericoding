-- <vc-preamble>
@[reducible, simp]
def BubbleSort_precond (a : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def swap (a : Array Int) (i j : Nat) : Array Int :=
  let temp := a[i]!
  let a₁ := a.set! i (a[j]!)
  a₁.set! j temp

def bubbleInner (j i : Nat) (a : Array Int) : Array Int :=
  if j < i then
    let a' := if a[j]! > a[j+1]! then swap a j (j+1) else a
    bubbleInner (j+1) i a'
  else
    a

def bubbleOuter (i : Nat) (a : Array Int) : Array Int :=
  if i > 0 then
    let a' := bubbleInner 0 i a
    bubbleOuter (i - 1) a'
  else
    a
-- </vc-helpers>

-- <vc-definitions>
def BubbleSort (a : Array Int) (h_precond : BubbleSort_precond (a)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def BubbleSort_postcond (a : Array Int) (result: Array Int) (h_precond : BubbleSort_precond (a)) :=
  List.Pairwise (· ≤ ·) result.toList ∧ List.isPerm result.toList a.toList

theorem BubbleSort_spec_satisfied (a: Array Int) (h_precond : BubbleSort_precond (a)) :
    BubbleSort_postcond (a) (BubbleSort (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>