-- <vc-preamble>
@[reducible]
def removeElement_precond (lst : List Nat) (target : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def removeElement (lst : List Nat) (target : Nat) (h_precond : removeElement_precond (lst) (target)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def removeElement_postcond (lst : List Nat) (target : Nat) (result: List Nat) (h_precond : removeElement_precond (lst) (target)): Prop :=
  -- 1. All elements equal to target are removed from the result.
  -- 2. All other elements are preserved in order.
  -- 3. No new elements are added.

  -- Helper predicate: result contains exactly the elements of lst that are not equal to target, in order
  let lst' := lst.filter (fun x => x ≠ target)
  result.zipIdx.all (fun (x, i) =>
    match lst'[i]? with
    | some y => x = y
    | none => false) ∧ result.length = lst'.length

theorem removeElement_spec_satisfied (lst: List Nat) (target: Nat) (h_precond : removeElement_precond (lst) (target)):
    removeElement_postcond (lst) (target) (removeElement (lst) (target) h_precond) h_precond := by
  sorry
-- </vc-theorems>