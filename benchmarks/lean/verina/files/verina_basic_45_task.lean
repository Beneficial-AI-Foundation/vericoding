-- <vc-preamble>
def isEven (n : Int) : Bool :=
  n % 2 = 0

def isOdd (n : Int) : Bool :=
  n % 2 ≠ 0

def firstEvenOddIndices (lst : List Int) : Option (Nat × Nat) :=
  let evenIndex := lst.findIdx? isEven
  let oddIndex := lst.findIdx? isOdd
  match evenIndex, oddIndex with
  | some ei, some oi => some (ei, oi)
  | _, _ => none
@[reducible, simp]
def findProduct_precond (lst : List Int) : Prop :=
  lst.length > 1 ∧
  (∃ x ∈ lst, isEven x) ∧
  (∃ x ∈ lst, isOdd x)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findProduct (lst : List Int) (h_precond : findProduct_precond (lst)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findProduct_postcond (lst : List Int) (result: Int) (h_precond : findProduct_precond (lst)) :=
  match firstEvenOddIndices lst with
  | some (ei, oi) => result = lst[ei]! * lst[oi]!
  | none => True

theorem findProduct_spec_satisfied (lst: List Int) (h_precond : findProduct_precond (lst)) :
    findProduct_postcond (lst) (findProduct (lst) h_precond) h_precond := by
  sorry
-- </vc-theorems>