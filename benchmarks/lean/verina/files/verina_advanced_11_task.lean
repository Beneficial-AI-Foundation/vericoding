-- <vc-preamble>
@[reducible, simp]
def findMajorityElement_precond (lst : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def countOccurrences (n : Int) (lst : List Int) : Nat :=
  lst.foldl (fun acc x => if x = n then acc + 1 else acc) 0
-- </vc-helpers>

-- <vc-definitions>
def findMajorityElement (lst : List Int) (h_precond : findMajorityElement_precond (lst)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def findMajorityElement_postcond (lst : List Int) (result: Int) (h_precond : findMajorityElement_precond (lst)) : Prop :=
  let count := fun x => (lst.filter (fun y => y = x)).length
  let n := lst.length
  let majority := count result > n / 2 ∧ lst.all (fun x => count x ≤ n / 2 ∨ x = result)
  (result = -1 → lst.all (count · ≤ n / 2) ∨ majority) ∧
  (result ≠ -1 → majority)

theorem findMajorityElement_spec_satisfied (lst: List Int) (h_precond : findMajorityElement_precond (lst)) :
    findMajorityElement_postcond (lst) (findMajorityElement (lst) h_precond) h_precond := by
  sorry
-- </vc-theorems>