import Mathlib
-- <vc-preamble>
-- Helper function declarations (assumed to exist)
noncomputable axiom SplitByNewlines : String → List String
noncomputable axiom SplitBySpaces : String → List String
noncomputable axiom StringToInt : String → Int

noncomputable def ValidInput (input : String) : Prop :=
  input.length > 0 ∧ input.data[input.length - 1]! = '\n' ∧
  let lines := SplitByNewlines input
  lines.length ≥ 2 ∧
  let firstLineParts := SplitBySpaces (lines[0]!)
  firstLineParts.length ≥ 2 ∧
  let m := StringToInt (firstLineParts[0]!)
  let n := StringToInt (firstLineParts[1]!)
  m ≥ 1 ∧ n ≥ 1 ∧ m + 1 < lines.length ∧
  ∀ dayIdx, 1 ≤ dayIdx ∧ dayIdx ≤ m →
    let dayLine := SplitBySpaces (lines[dayIdx.natAbs]!)
    dayLine.length ≥ 1 ∧
    let s := StringToInt (dayLine[0]!)
    s ≥ 1 ∧ s < n ∧ s + 1 ≤ dayLine.length ∧
    ∀ storeIdx, 1 ≤ storeIdx ∧ storeIdx ≤ s →
      let store := StringToInt (dayLine[storeIdx.natAbs]!)
      1 ≤ store ∧ store ≤ n

noncomputable def ExtractDoraSet (input : String) (dayIndex : Int) (n : Int) : List Int :=
  if input.length > 0 ∧ dayIndex ≥ 0 ∧ n ≥ 1 then
    let lines := SplitByNewlines input
    if dayIndex + 1 ≥ lines.length then []
    else
      let dayLine := SplitBySpaces (lines[(dayIndex + 1).natAbs]!)
      if dayLine.length ≤ 1 then []
      else
        let s := StringToInt (dayLine[0]!)
        if s + 1 > dayLine.length then []
        else
          (List.range s.natAbs).map (fun i => StringToInt (dayLine[i + 1]!))
  else []

noncomputable def ExtractSwiperSet (input : String) (dayIndex : Int) (n : Int) : List Int :=
  if input.length > 0 ∧ dayIndex ≥ 0 ∧ n ≥ 1 then
    let allStores := (List.range n.natAbs).map (fun x => Int.ofNat (x + 1))
    let doraSet := ExtractDoraSet input dayIndex n
    allStores.filter (fun x => x ∉ doraSet)
  else []

noncomputable def SolutionExists (input : String) : Prop :=
  let lines := SplitByNewlines input
  let firstLineParts := SplitBySpaces (lines[0]!)
  let m := StringToInt (firstLineParts[0]!)
  let n := StringToInt (firstLineParts[1]!)
  ∀ i j, 0 ≤ i ∧ i < m ∧ 0 ≤ j ∧ j < m →
    ¬(∀ x, x ∈ ExtractDoraSet input i n → x ∈ ExtractSwiperSet input j n)

@[reducible, simp]
noncomputable def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
namespace VCHelpers
/-- Classical excluded-middle for SolutionExists, useful for case splits in proofs. -/
theorem byCasesSolutionExists (input : String) :
    SolutionExists input ∨ ¬ SolutionExists input :=
  Classical.em _
end VCHelpers
-- </vc-helpers>

-- <vc-definitions>
noncomputable def solve (input : String) (h_precond : solve_precond input) : String :=
  by
  classical
  exact (if SolutionExists input then "possible" else "impossible")
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
noncomputable def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  (result = "possible" ∨ result = "impossible") ∧
  (result = "possible" ↔ SolutionExists input)

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  classical
by_cases h : SolutionExists input
· simp [solve_postcond, solve, h]
· simp [solve_postcond, solve, h]
-- </vc-theorems>
