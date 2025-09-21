-- <vc-preamble>
def ValidDungeon (dungeon : List (List Int)) : Prop :=
  dungeon.length > 0 ∧
  (∀ i, 0 ≤ i ∧ i < Int.ofNat dungeon.length → dungeon[i.toNat]!.length > 0) ∧
  (∀ i, 0 ≤ i ∧ i < Int.ofNat dungeon.length → dungeon[i.toNat]!.length = dungeon[0]!.length)

def isValidPath (dungeon : List (List Int)) (path : List (Int × Int)) : Prop :=
  ValidDungeon dungeon →
  path.length > 0 ∧
  path[0]! = (0, 0) ∧
  path[path.length - 1]! = (Int.ofNat (dungeon.length - 1), Int.ofNat (dungeon[0]!.length - 1)) ∧
  (∀ i, 0 ≤ i ∧ i < Int.ofNat path.length → 
      let (r, c) := path[i.toNat]!
      0 ≤ r ∧ r < Int.ofNat dungeon.length ∧ 0 ≤ c ∧ c < Int.ofNat dungeon[0]!.length) ∧
  ∀ i, 0 ≤ i ∧ i < Int.ofNat (path.length - 1) → 
      (path[i.toNat]!.2 = path[(i+1).toNat]!.2 ∧ path[i.toNat]!.1 + 1 = path[(i+1).toNat]!.1) ∨
      (path[i.toNat]!.1 = path[(i+1).toNat]!.1 ∧ path[i.toNat]!.2 + 1 = path[(i+1).toNat]!.2)

def healthAtStep (dungeon : List (List Int)) (path : List (Int × Int)) (step : Nat) (initialHealth : Int) : Int :=
  match step with
  | 0 => 
      let (r, c) := path[0]!
      initialHealth + dungeon[r.toNat]![c.toNat]!
  | step' + 1 =>
      let (r, c) := path[step]!
      healthAtStep dungeon path step' initialHealth + dungeon[r.toNat]![c.toNat]!

def canSurvivePath (dungeon : List (List Int)) (path : List (Int × Int)) (initialHealth : Int) : Prop :=
  ValidDungeon dungeon ∧ isValidPath dungeon path →
  ∀ i, 0 ≤ i ∧ i < Int.ofNat path.length → 
      healthAtStep dungeon path i.toNat initialHealth > 0

@[reducible, simp]
def solve_precond (dungeon : List (List Int)) : Prop :=
  ValidDungeon dungeon
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (dungeon : List (List Int)) (h_precond : solve_precond dungeon) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (dungeon : List (List Int)) (result: Int) (h_precond : solve_precond dungeon) : Prop :=
  result ≥ 1

theorem solve_spec_satisfied (dungeon : List (List Int)) (h_precond : solve_precond dungeon) :
    solve_postcond dungeon (solve dungeon h_precond) h_precond := by
  sorry
-- </vc-theorems>