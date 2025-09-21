-- <vc-preamble>
-- Helper functions (axiomatized for now)
axiom SplitLinesFunc : String → List String
axiom ParseIntFunc : String → Int
axiom ParseIntArrayFunc : String → List Int
axiom IntToStringFunc : Int → String
axiom SplitLinesHelper : String → Int → String → List String → List String
axiom ParseIntHelper : String → Int → Int → Int
axiom ParseIntArrayHelper : String → Int → String → List Int → List Int
axiom IntToStringHelper : Int → String → String
axiom gcd : Int → Int → Int

-- Properties of helper functions
axiom SplitLinesFunc_prop : ∀ s, ∀ line, line ∈ SplitLinesFunc s → True
axiom ParseIntFunc_nonneg : ∀ s, ParseIntFunc s ≥ 0
axiom ParseIntArrayFunc_nonneg : ∀ s, ∀ x, x ∈ ParseIntArrayFunc s → x ≥ 0
axiom gcd_pos : ∀ a b, a > 0 → b > 0 → gcd a b > 0

noncomputable def ValidInput (input : String) : Prop :=
  let lines := SplitLinesFunc input
  lines.length ≥ 3 ∧
  ParseIntFunc (lines[0]!) > 0 ∧
  ParseIntFunc (lines[2]!) ≥ 0 ∧
  lines.length ≥ 3 + (ParseIntFunc (lines[2]!)).toNat ∧
  (ParseIntArrayFunc (lines[1]!)).length = (ParseIntFunc (lines[0]!)).toNat ∧
  (∀ i, 0 ≤ i ∧ i < (ParseIntArrayFunc (lines[1]!)).length → (ParseIntArrayFunc (lines[1]!))[i]! > 0) ∧
  (∀ i, 0 ≤ i ∧ i < (ParseIntFunc (lines[2]!)).toNat → ParseIntFunc (lines[(3 + i)]!) > 0)

def SubarrayPairs (arr : List Int) : List (Nat × Nat) :=
  List.range arr.length |>.foldl (fun acc i =>
    acc ++ (List.range arr.length |>.map (fun j => if i ≤ j then (i, j) else (0, 0)) |>.filter (fun p => p.1 ≤ p.2))) []

noncomputable def SubarrayGCD (arr : List Int) (start end_ : Nat) : Int :=
  if h : start ≥ end_ then arr[start]!
  else gcd arr[start]! (SubarrayGCD arr (start + 1) end_)
  termination_by end_ - start

noncomputable def CountSubarraysWithGCD (arr : List Int) (_ : Int) : Int :=
  (SubarrayPairs arr).length

noncomputable def GetExpectedResults (input : String) : List Int :=
  let lines := SplitLinesFunc input
  let arr := ParseIntArrayFunc (lines[1]!)
  let q := ParseIntFunc (lines[2]!)
  List.range q.toNat |>.map (fun i => CountSubarraysWithGCD arr (ParseIntFunc (lines[(3 + i)]!)))

noncomputable def FormatOutput (results : List Int) : String :=
  String.intercalate "\n" (results.map IntToStringFunc)

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
noncomputable def solve (input : String) (_ : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (_ : solve_precond input) : Prop :=
  result = FormatOutput (GetExpectedResults input)

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>