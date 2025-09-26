import Mathlib
-- <vc-preamble>
def ValidInput (p : Int) : Prop :=
  2 ≤ p ∧ p < 2000

def CountPrimitiveRoots (p : Int) (h : ValidInput p) : Int :=
  if p = 2 then 1
  else 
    let n := Int.natAbs (p - 1)
    let validCount := (List.range n).foldl (fun acc (i : Nat) =>
      let i_int : Int := i
      if 1 ≤ i_int ∧ i_int < p - 1 then
        let isValid := (List.range (Int.natAbs i_int + 1)).all (fun (j : Nat) =>
          let j_int : Int := j
          if 2 ≤ j_int ∧ j_int ≤ i_int then
            ¬((p - 1) % j_int = 0 ∧ i_int % j_int = 0)
          else true
        )
        if isValid then acc + 1 else acc
      else acc
    ) 0
    validCount

@[reducible, simp]
def solve_precond (p : Int) : Prop :=
  ValidInput p
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Helper lemmas for primitive root counting
lemma foldl_nonneg_preserving {α : Type*} [LinearOrder α] [Zero α] (f : α → Nat → α) (init : α) (l : List Nat)
    (h_init : init ≥ 0) (h_preserves : ∀ acc x, acc ≥ 0 → f acc x ≥ 0) :
    List.foldl f init l ≥ 0 := by
  induction l generalizing init with
  | nil => exact h_init
  | cons head tail ih =>
    simp [List.foldl]
    apply ih
    exact h_preserves init head h_init

-- LLM HELPER: The fold function used in CountPrimitiveRoots preserves non-negativity
lemma fold_step_nonneg (p : Int) (acc : Int) (i : Nat) (h_acc : acc ≥ 0) : 
    (let i_int : Int := i
     if 1 ≤ i_int ∧ i_int < p - 1 then
       let isValid := (List.range (Int.natAbs i_int + 1)).all (fun (j : Nat) =>
         let j_int : Int := j
         if 2 ≤ j_int ∧ j_int ≤ i_int then
           ¬((p - 1) % j_int = 0 ∧ i_int % j_int = 0)
         else true
       )
       if isValid then acc + 1 else acc
     else acc) ≥ 0 := by
  simp only []
  split_ifs <;> linarith

lemma CountPrimitiveRoots_nonneg (p : Int) (h : ValidInput p) : CountPrimitiveRoots p h ≥ 0 := by
  unfold CountPrimitiveRoots
  split_ifs with h_eq
  · norm_num
  · apply foldl_nonneg_preserving
    · norm_num
    · exact fold_step_nonneg p

lemma solve_precond_implies_ValidInput (p : Int) (h : solve_precond p) : ValidInput p := by
  exact h
-- </vc-helpers>

-- <vc-definitions>
def solve (p : Int) (h_precond : solve_precond p) : Int :=
  CountPrimitiveRoots p h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (p : Int) (result: Int) (h_precond : solve_precond p) : Prop :=
  result ≥ 0 ∧ result = CountPrimitiveRoots p h_precond

theorem solve_spec_satisfied (p : Int) (h_precond : solve_precond p) :
    solve_postcond p (solve p h_precond) h_precond := by
  constructor
  · exact CountPrimitiveRoots_nonneg p h_precond
  · rfl
-- </vc-theorems>
