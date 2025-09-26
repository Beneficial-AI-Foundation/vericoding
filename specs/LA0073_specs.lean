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
-- </vc-helpers>

-- <vc-definitions>
def solve (reps : List Int) (h_precond : solve_precond reps) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (reps : List Int) (result : String) (h_precond : solve_precond reps) : Prop :=
  (result = "chest" ∨ result = "biceps" ∨ result = "back") ∧ 
  IsWinner result reps h_precond

theorem solve_spec_satisfied (reps : List Int) (h_precond : solve_precond reps) :
    solve_postcond reps (solve reps h_precond) h_precond := by
  sorry
-- </vc-theorems>