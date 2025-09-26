-- <vc-preamble>
@[reducible, simp]
def SlopeSearch_precond (a : Array (Array Int)) (key : Int) : Prop :=
  List.Pairwise (·.size = ·.size) a.toList ∧
  a.all (fun x => List.Pairwise (· ≤ ·) x.toList) ∧
  (
    a.size = 0 ∨ (
      (List.range (a[0]!.size)).all (fun i =>
        List.Pairwise (· ≤ ·) (a.map (fun x => x[i]!)).toList
      )
    )
  )
-- </vc-preamble>

-- <vc-helpers>
@[reducible, simp]
def get2d (a : Array (Array Int)) (i j : Int) : Int :=
  (a[Int.toNat i]!)[Int.toNat j]!
-- </vc-helpers>

-- <vc-definitions>
def SlopeSearch (a : Array (Array Int)) (key : Int) (h_precond : SlopeSearch_precond (a) (key)) : (Int × Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def SlopeSearch_postcond (a : Array (Array Int)) (key : Int) (result: (Int × Int)) (h_precond : SlopeSearch_precond (a) (key)) :=
  let (m, n) := result;
  (m ≥ 0 ∧ m < a.size ∧ n ≥ 0 ∧ n < (a[0]!).size ∧ get2d a m n = key) ∨
  (m = -1 ∧ n = -1 ∧ a.all (fun x => x.all (fun e => e ≠ key)))

theorem SlopeSearch_spec_satisfied (a: Array (Array Int)) (key: Int) (h_precond : SlopeSearch_precond (a) (key)) :
    SlopeSearch_postcond (a) (key) (SlopeSearch (a) (key) h_precond) h_precond := by
  sorry
-- </vc-theorems>