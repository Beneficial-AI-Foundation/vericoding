import Mathlib
-- <vc-preamble>
def CountOccurrences : List Int → Int → Int
  | [], _ => 0
  | x :: xs, target => if x = target then 1 + CountOccurrences xs target else CountOccurrences xs target

def ListSum : List Int → Int
  | [] => 0
  | x :: xs => x + ListSum xs

def ValidInput (n : Int) (ratings : List Int) : Prop :=
  n ≥ 2 ∧ ratings.length = Int.natAbs n

def AllInfected (k : Int) (ratings : List Int) : Prop :=
  k ∈ ratings ∧ CountOccurrences ratings k = ratings.length

def CanInfectInOneContest (k : Int) (ratings : List Int) : Prop :=
  (k ∈ ratings ∧ CountOccurrences ratings k ≠ ratings.length) ∨
  (k ∉ ratings ∧ k * (ratings.length : Int) = ListSum ratings)

def RequiresTwoContests (k : Int) (ratings : List Int) : Prop :=
  k ∉ ratings ∧ k * (ratings.length : Int) ≠ ListSum ratings

@[reducible, simp]
def solve_precond (n : Int) (k : Int) (ratings : List Int) : Prop :=
  ValidInput n ratings
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Decidability instances
instance decidableAllInfected (k : Int) (ratings : List Int) : Decidable (AllInfected k ratings) := by
  unfold AllInfected
  infer_instance

instance decidableCanInfectInOneContest (k : Int) (ratings : List Int) : Decidable (CanInfectInOneContest k ratings) := by
  unfold CanInfectInOneContest
  infer_instance

instance decidableRequiresTwoContests (k : Int) (ratings : List Int) : Decidable (RequiresTwoContests k ratings) := by
  unfold RequiresTwoContests
  infer_instance

-- LLM HELPER
-- Helper lemma for mutual exclusivity of cases
lemma infection_cases_exclusive (k : Int) (ratings : List Int) :
  (AllInfected k ratings → ¬CanInfectInOneContest k ratings ∧ ¬RequiresTwoContests k ratings) ∧
  (CanInfectInOneContest k ratings → ¬AllInfected k ratings ∧ ¬RequiresTwoContests k ratings) ∧
  (RequiresTwoContests k ratings → ¬AllInfected k ratings ∧ ¬CanInfectInOneContest k ratings) := by
  constructor
  · intro h_all
    constructor
    · intro h_one
      unfold AllInfected CanInfectInOneContest at *
      cases h_one with
      | inl h_left => 
        have h_count := h_left.2
        have h_all_count := h_all.2
        exact h_count h_all_count
      | inr h_right =>
        have h_not_in := h_right.1
        have h_in := h_all.1
        exact h_not_in h_in
    · intro h_two
      unfold AllInfected RequiresTwoContests at *
      have h_in := h_all.1
      have h_not_in := h_two.1
      exact h_not_in h_in
  constructor
  · intro h_one
    constructor
    · intro h_all
      unfold AllInfected CanInfectInOneContest at *
      cases h_one with
      | inl h_left =>
        have h_count := h_left.2
        have h_all_count := h_all.2
        exact h_count h_all_count
      | inr h_right =>
        have h_not_in := h_right.1
        have h_in := h_all.1
        exact h_not_in h_in
    · intro h_two
      unfold CanInfectInOneContest RequiresTwoContests at *
      cases h_one with
      | inl h_left =>
        have h_in := h_left.1
        have h_not_in := h_two.1
        exact h_not_in h_in
      | inr h_right =>
        have h_eq := h_right.2
        have h_neq := h_two.2
        exact h_neq h_eq
  · intro h_two
    constructor
    · intro h_all
      unfold AllInfected RequiresTwoContests at *
      have h_in := h_all.1
      have h_not_in := h_two.1
      exact h_not_in h_in
    · intro h_one
      unfold CanInfectInOneContest RequiresTwoContests at *
      cases h_one with
      | inl h_left =>
        have h_in := h_left.1
        have h_not_in := h_two.1
        exact h_not_in h_in
      | inr h_right =>
        have h_eq := h_right.2
        have h_neq := h_two.2
        exact h_neq h_eq
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (k : Int) (ratings : List Int) (h_precond : solve_precond n k ratings) : Int :=
  if AllInfected k ratings then 0
  else if CanInfectInOneContest k ratings then 1
  else 2
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (k : Int) (ratings : List Int) (result : Int) (h_precond : solve_precond n k ratings) : Prop :=
  result ≥ 0 ∧ result ≤ 2 ∧
  (AllInfected k ratings → result = 0) ∧
  (CanInfectInOneContest k ratings ∧ ¬AllInfected k ratings → result = 1) ∧
  (RequiresTwoContests k ratings → result = 2)

theorem solve_spec_satisfied (n : Int) (k : Int) (ratings : List Int) (h_precond : solve_precond n k ratings) :
    solve_postcond n k ratings (solve n k ratings h_precond) h_precond := by
  unfold solve solve_postcond
  constructor
  · -- result ≥ 0
    by_cases h_all : AllInfected k ratings
    · simp [h_all]
    · by_cases h_one : CanInfectInOneContest k ratings
      · simp [h_all, h_one]
      · simp [h_all, h_one]
  constructor
  · -- result ≤ 2
    by_cases h_all : AllInfected k ratings
    · simp [h_all]
    · by_cases h_one : CanInfectInOneContest k ratings
      · simp [h_all, h_one]
      · simp [h_all, h_one]
  constructor
  · -- AllInfected case
    intro h_all
    simp [h_all]
  constructor
  · -- CanInfectInOneContest case
    intro ⟨h_can, h_not_all⟩
    simp [h_not_all, h_can]
  · -- RequiresTwoContests case
    intro h_two
    have h_excl := infection_cases_exclusive k ratings
    have h_not_all := h_excl.2.2 h_two |>.1
    have h_not_can := h_excl.2.2 h_two |>.2
    simp [h_not_all, h_not_can]
-- </vc-theorems>
