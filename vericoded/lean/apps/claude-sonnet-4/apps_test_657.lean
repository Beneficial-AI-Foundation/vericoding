import Mathlib
-- <vc-preamble>
def mymax (a b : Int) : Int :=
  if a ≥ b then a else b

def ValidInput (a b x y z : Int) : Prop :=
  a ≥ 0 ∧ b ≥ 0 ∧ x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0

def YellowCrystalsNeeded (x y : Int) : Int :=
  x * 2 + y

def BlueCrystalsNeeded (y z : Int) : Int :=
  y + z * 3

def MinAdditionalCrystals (a b x y z : Int) : Int :=
  mymax 0 (YellowCrystalsNeeded x y - a) + mymax 0 (BlueCrystalsNeeded y z - b)

@[reducible, simp]
def solve_precond (a b x y z : Int) : Prop :=
  ValidInput a b x y z
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Lemmas for mymax properties
lemma mymax_nonneg (a b : Int) (ha : a ≥ 0) (hb : b ≥ 0) : mymax a b ≥ 0 := by
  unfold mymax
  split_ifs with h
  · exact ha
  · exact hb

lemma mymax_zero_nonneg (a : Int) : mymax 0 a ≥ 0 := by
  unfold mymax
  split_ifs
  · rfl
  · linarith

lemma MinAdditionalCrystals_nonneg (a b x y z : Int) (h : ValidInput a b x y z) :
    MinAdditionalCrystals a b x y z ≥ 0 := by
  unfold MinAdditionalCrystals
  apply add_nonneg
  · exact mymax_zero_nonneg _
  · exact mymax_zero_nonneg _
-- </vc-helpers>

-- <vc-definitions>
def solve (a b x y z : Int) (h_precond : solve_precond a b x y z) : Int :=
  MinAdditionalCrystals a b x y z
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b x y z : Int) (result: Int) (h_precond : solve_precond a b x y z) : Prop :=
  result ≥ 0 ∧ result = MinAdditionalCrystals a b x y z

theorem solve_spec_satisfied (a b x y z : Int) (h_precond : solve_precond a b x y z) :
    solve_postcond a b x y z (solve a b x y z h_precond) h_precond := by
  unfold solve_postcond
  constructor
  · -- Prove result ≥ 0
    exact MinAdditionalCrystals_nonneg a b x y z h_precond
  · -- Prove result = MinAdditionalCrystals a b x y z
    rfl
-- </vc-theorems>
