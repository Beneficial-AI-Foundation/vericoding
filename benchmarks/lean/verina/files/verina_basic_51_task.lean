-- <vc-preamble>
@[reducible, simp]
def BinarySearch_precond (a : Array Int) (key : Int) : Prop :=
  List.Pairwise (· ≤ ·) a.toList
-- </vc-preamble>

-- <vc-helpers>
def binarySearchLoop (a : Array Int) (key : Int) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if (a[mid]! < key) then binarySearchLoop a key (mid + 1) hi
    else binarySearchLoop a key lo mid
  else
    lo
-- </vc-helpers>

-- <vc-definitions>
def BinarySearch (a : Array Int) (key : Int) (h_precond : BinarySearch_precond (a) (key)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def BinarySearch_postcond (a : Array Int) (key : Int) (result: Nat) (h_precond : BinarySearch_precond (a) (key)) :=
  result ≤ a.size ∧
  ((a.take result).all (fun x => x < key)) ∧
  ((a.drop result).all (fun x => x ≥ key))

theorem BinarySearch_spec_satisfied (a: Array Int) (key: Int) (h_precond : BinarySearch_precond (a) (key)) :
    BinarySearch_postcond (a) (key) (BinarySearch (a) (key) h_precond) h_precond := by
  sorry
-- </vc-theorems>