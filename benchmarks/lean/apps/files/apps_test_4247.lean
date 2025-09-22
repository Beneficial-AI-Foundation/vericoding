-- <vc-preamble>
def ValidInput (n : Int) (p : List Int) : Prop :=
  p.length = n ∧ n ≥ 3

def IsMedianOfThree (a b c : Int) : Bool :=
  (a < b && b < c) || (a > b && b > c)

def CountMedianElements (p : List Int) (n : Int) : Int :=
  if n ≥ 3 then
    (List.range (Int.natAbs (n - 2))).filter (fun i => 
      let idx := Int.ofNat i
      if h : idx.natAbs < p.length ∧ (idx + 1).natAbs < p.length ∧ (idx + 2).natAbs < p.length then
        IsMedianOfThree (p.get ⟨idx.natAbs, h.1⟩) (p.get ⟨(idx + 1).natAbs, h.2.1⟩) (p.get ⟨(idx + 2).natAbs, h.2.2⟩)
      else 
        false) |>.length
  else 0

@[reducible, simp]
def solve_precond (n : Int) (p : List Int) : Prop :=
  ValidInput n p
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (p : List Int) (h_precond : solve_precond n p) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (p : List Int) (result : Int) (h_precond : solve_precond n p) : Prop :=
  result ≥ 0 ∧ result ≤ n - 2 ∧ result = CountMedianElements p n

theorem solve_spec_satisfied (n : Int) (p : List Int) (h_precond : solve_precond n p) :
    solve_postcond n p (solve n p h_precond) h_precond := by
  sorry
-- </vc-theorems>