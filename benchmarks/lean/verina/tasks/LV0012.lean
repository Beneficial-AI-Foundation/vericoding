-- <vc-preamble>
@[reducible]
def hasChordIntersection_precond (N : Nat) (chords : List (List Nat)) : Prop :=
  N ≥ 2 ∧
  chords.all (fun chord => chord.length = 2 ∧ chord[0]! ≥ 1 ∧ chord[0]! ≤ 2 * N ∧ chord[1]! ≥ 1 ∧ chord[1]! ≤ 2 * N) ∧
  List.Nodup (chords.flatMap id)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hasChordIntersection (N : Nat) (chords : List (List Nat)) (h_precond : hasChordIntersection_precond (N) (chords)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def hasChordIntersection_postcond (N : Nat) (chords : List (List Nat)) (result: Bool) (h_precond : hasChordIntersection_precond (N) (chords)) : Prop :=
  let sortedChords := chords.map (fun chord =>
    let a := chord[0]!
    let b := chord[1]!
    if a > b then [b, a] else [a, b]
  )

  let rec hasIntersection (chord1 : List Nat) (chord2 : List Nat) : Bool :=
    let a1 := chord1[0]!
    let b1 := chord1[1]!
    let a2 := chord2[0]!
    let b2 := chord2[1]!
    (a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1)

  let rec checkAllPairs (chords : List (List Nat)) : Bool :=
    match chords with
    | [] => false
    | x :: xs =>
      if xs.any (fun y => hasIntersection x y) then true
      else checkAllPairs xs

  ((List.Pairwise (fun x y => !hasIntersection x y) sortedChords) → ¬ result) ∧
  ((sortedChords.any (fun x => chords.any (fun y => hasIntersection x y))) → result)

theorem hasChordIntersection_spec_satisfied (N: Nat) (chords: List (List Nat)) (h_precond : hasChordIntersection_precond (N) (chords)) :
    hasChordIntersection_postcond (N) (chords) (hasChordIntersection (N) (chords) h_precond) h_precond := by
  sorry
-- </vc-theorems>