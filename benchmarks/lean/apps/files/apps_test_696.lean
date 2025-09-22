-- <vc-preamble>
def ValidInput (p : Int) : Prop :=
  2 ≤ p ∧ p < 2000

def CountPrimitiveRoots (p : Int) (h : ValidInput p) : Int :=
  if p = 2 then 1
  else 
    let n := Int.natAbs (p - 1)
    let validCount := (List.range n).foldl (fun acc (i : Nat) =>
      let i_int : Int := i
      if 1 ≤ i_int ∧ i_int < p - 1 then
        let isValid := (List.range (Int.natAbs i_int + 1)).all (fun (j : Nat) =>
          let j_int : Int := j
          if 2 ≤ j_int ∧ j_int ≤ i_int then
            ¬((p - 1) % j_int = 0 ∧ i_int % j_int = 0)
          else true
        )
        if isValid then acc + 1 else acc
      else acc
    ) 0
    validCount

@[reducible, simp]
def solve_precond (p : Int) : Prop :=
  ValidInput p
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (p : Int) (h_precond : solve_precond p) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (p : Int) (result: Int) (h_precond : solve_precond p) : Prop :=
  result ≥ 0 ∧ result = CountPrimitiveRoots p h_precond

theorem solve_spec_satisfied (p : Int) (h_precond : solve_precond p) :
    solve_postcond p (solve p h_precond) h_precond := by
  sorry
-- </vc-theorems>