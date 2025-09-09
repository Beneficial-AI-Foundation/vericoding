@[reducible, simp]
def update_map_precond (m1 : Map Int Int) (m2 : Map Int Int) : Prop :=
  True

-- <vc-helpers>
-- </vc-helpers>

def update_map (m1 : Map Int Int) (m2 : Map Int Int) (h_precond : update_map_precond (m1) (m2)) : Map Int Int :=
  sorry

def find? {K V : Type} [BEq K] [BEq V] (m : Map K V) (k : K) : Option V :=
  m.entries.find? (fun p => p.1 == k) |>.map (·.2)
@[reducible, simp]
def update_map_postcond (m1 : Map Int Int) (m2 : Map Int Int) (result: Map Int Int) (h_precond : update_map_precond (m1) (m2)) : Prop :=
  List.Pairwise (fun a b => a.1 ≤ b.1) result.entries ∧
  m2.entries.all (fun x => find? result x.1 = some x.2) ∧
  m1.entries.all (fun x =>
    match find? m2 x.1 with
    | some _ => true
    | none => find? result x.1 = some x.2
  ) ∧
  result.entries.all (fun x =>
    match find? m1 x.1 with
    | some v => match find? m2 x.1 with
      | some v' => x.2 = v'
      | none => x.2 = v
    | none => find? m2 x.1 = some x.2
  )

theorem update_map_spec_satisfied (m1: Map Int Int) (m2: Map Int Int) (h_precond : update_map_precond (m1) (m2)) :
    update_map_postcond (m1) (m2) (update_map (m1) (m2) h_precond) h_precond := by
  sorry

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "m1": "⟨[(1, 10), (2, 20)]⟩",
            "m2": "⟨[(2, 30), (3, 40)]⟩"
        },
        "expected": "⟨[(1, 10), (2, 30), (3, 40)]⟩",
        "unexpected": [
            "⟨[(1, 10), (2, 20), (3, 40)]⟩",
            "⟨[(1, 10), (2, 20)]⟩",
            "⟨[(2, 30), (3, 40)]⟩"
        ]
    },
    {
        "input": {
            "m1": "⟨[(1, 100)]⟩",
            "m2": "⟨[(1, 200)]⟩"
        },
        "expected": "⟨[(1, 200)]⟩",
        "unexpected": [
            "⟨[(1, 100)]⟩",
            "⟨[(1, 200), (1, 100)]⟩",
            "⟨[]⟩"
        ]
    },
    {
        "input": {
            "m1": "⟨[(5, 50), (6, 60)]⟩",
            "m2": "⟨[]⟩"
        },
        "expected": "⟨[(5, 50), (6, 60)]⟩",
        "unexpected": [
            "⟨[(5, 50)]⟩",
            "⟨[(6, 60)]⟩",
            "⟨[(5, 50), (6, 60), (7, 70)]⟩"
        ]
    },
    {
        "input": {
            "m1": "⟨[]⟩",
            "m2": "⟨[(7, 70)]⟩"
        },
        "expected": "⟨[(7, 70)]⟩",
        "unexpected": [
            "⟨[]⟩",
            "⟨[(0, 70)]⟩",
            "⟨[(7, 0)]⟩"
        ]
    },
    {
        "input": {
            "m1": "⟨[(1, 1), (2, 2), (3, 3)]⟩",
            "m2": "⟨[(2, 20), (4, 40)]⟩"
        },
        "expected": "⟨[(1, 1), (2, 20), (3, 3), (4, 40)]⟩",
        "unexpected": [
            "⟨[(1, 1), (2, 2), (3, 3)]⟩",
            "⟨[(1, 1), (2, 20), (3, 3)]⟩",
            "⟨[(1, 1), (2, 20), (3, 3), (4, 30)]⟩"
        ]
    }
]
-/