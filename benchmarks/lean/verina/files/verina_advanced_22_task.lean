-- <vc-preamble>
@[reducible, simp]
def isPeakValley_precond (lst : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPeakValley (lst : List Int) (h_precond : isPeakValley_precond (lst)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isPeakValley_postcond (lst : List Int) (result: Bool) (h_precond : isPeakValley_precond (lst)) : Prop :=
  let len := lst.length
  let validPeaks :=
    List.range len |>.filter (fun p =>
      1 ≤ p ∧ p < len - 1 ∧

      -- check strictly increasing before peak
      (List.range p).all (fun i =>
        lst[i]! < lst[i + 1]!
      ) ∧

      -- check strictly decreasing after peak
      (List.range (len - 1 - p)).all (fun i =>
        lst[p + i]! > lst[p + i + 1]!
      )
    )
  (validPeaks != [] → result) ∧
  (validPeaks.length = 0 → ¬ result)

theorem isPeakValley_spec_satisfied (lst: List Int) (h_precond : isPeakValley_precond (lst)) :
    isPeakValley_postcond (lst) (isPeakValley (lst) h_precond) h_precond := by
  sorry
-- </vc-theorems>