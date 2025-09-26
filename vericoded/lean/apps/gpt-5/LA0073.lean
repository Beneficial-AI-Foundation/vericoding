import Mathlib
-- <vc-preamble>

def ChestTotal (reps : List Int) : Int :=
  (List.range reps.length).map (fun i => if i % 3 = 0 then reps[i]! else 0) |>.sum

def BicepsTotal (reps : List Int) : Int :=
  (List.range reps.length).map (fun i => if i % 3 = 1 then reps[i]! else 0) |>.sum

def BackTotal (reps : List Int) : Int :=
  (List.range reps.length).map (fun i => if i % 3 = 2 then reps[i]! else 0) |>.sum

def ValidInput (reps : List Int) : Prop :=
  reps.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < reps.length → reps[i]! > 0

def IsWinner (muscle : String) (reps : List Int) (h_valid : ValidInput reps) : Prop :=
  let chestTotal := ChestTotal reps
  let bicepsTotal := BicepsTotal reps  
  let backTotal := BackTotal reps
  match muscle with
  | "chest" => chestTotal ≥ bicepsTotal ∧ chestTotal ≥ backTotal
  | "biceps" => bicepsTotal > chestTotal ∧ bicepsTotal ≥ backTotal
  | "back" => backTotal > chestTotal ∧ backTotal > bicepsTotal
  | _ => False

@[reducible, simp]
def solve_precond (reps : List Int) : Prop :=
  ValidInput reps
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma back_strict_max_of_not_chest_and_not_biceps
  {c b k : Int}
  (h1 : ¬ (c ≥ b ∧ c ≥ k))
  (h2 : ¬ (b > c ∧ b ≥ k)) :
  k > c ∧ k > b := by
  classical
  have hc_lt_b_or_lt_k : c < b ∨ c < k := by
    by_cases hb : c ≥ b
    · have : ¬ c ≥ k := by
        intro hk
        exact h1 ⟨hb, hk⟩
      exact Or.inr (lt_of_not_ge this)
    · exact Or.inl (lt_of_not_ge hb)
  have hk_gt_c : k > c := by
    cases hc_lt_b_or_lt_k with
    | inr hc_lt_k => exact hc_lt_k
    | inl hc_lt_b =>
        have hb_not_ge : ¬ b ≥ k := by
          intro hbk
          have bgtc : b > c := hc_lt_b
          exact h2 ⟨bgtc, hbk⟩
        have hb_lt_k : b < k := lt_of_not_ge hb_not_ge
        exact lt_trans hc_lt_b hb_lt_k
  have hk_gt_b : k > b := by
    by_cases hbk : b ≥ k
    · have hb_not_gt_c : ¬ b > c := by
        intro hgt
        exact h2 ⟨hgt, hbk⟩
      have hb_le_c : b ≤ c := le_of_not_gt hb_not_gt_c
      exact lt_of_le_of_lt hb_le_c hk_gt_c
    · exact lt_of_not_ge hbk
  exact ⟨hk_gt_c, hk_gt_b⟩
-- </vc-helpers>

-- <vc-definitions>
def solve (reps : List Int) (h_precond : solve_precond reps) : String :=
  let chestTotal := ChestTotal reps
let bicepsTotal := BicepsTotal reps
let backTotal := BackTotal reps
if h1 : chestTotal ≥ bicepsTotal ∧ chestTotal ≥ backTotal then
  "chest"
else if h2 : bicepsTotal > chestTotal ∧ bicepsTotal ≥ backTotal then
  "biceps"
else
  "back"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (reps : List Int) (result : String) (h_precond : solve_precond reps) : Prop :=
  (result = "chest" ∨ result = "biceps" ∨ result = "back") ∧ 
  IsWinner result reps h_precond

theorem solve_spec_satisfied (reps : List Int) (h_precond : solve_precond reps) :
    solve_postcond reps (solve reps h_precond) h_precond := by
  classical
dsimp [solve_postcond]
by_cases h1 : ChestTotal reps ≥ BicepsTotal reps ∧ ChestTotal reps ≥ BackTotal reps
· constructor
  · simp [solve, h1]
  · simpa [solve, IsWinner, h1] using h1
· by_cases h2 : BicepsTotal reps > ChestTotal reps ∧ BicepsTotal reps ≥ BackTotal reps
  · constructor
    · simp [solve, h1, h2]
    · simpa [solve, IsWinner, h1, h2] using h2
  · constructor
    · simp [solve, h1, h2]
    ·
      have hb := back_strict_max_of_not_chest_and_not_biceps
        (c := ChestTotal reps) (b := BicepsTotal reps) (k := BackTotal reps) h1 h2
      rcases hb with ⟨hk_gt_c, hk_gt_b⟩
      simpa [solve, IsWinner, h1, h2] using And.intro hk_gt_c hk_gt_b
-- </vc-theorems>
