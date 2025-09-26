import Mathlib
-- <vc-preamble>
/- Precondition for count_true -/
@[reducible, simp]
def countTrue_precond (arr : Array Bool) : Prop := True

/- Helper function to count boolean values -/
def countBoolean (seq : List Bool) : Int :=
  match seq with
  | [] => 0
  | hd :: tl => countBoolean tl + if hd then 1 else 0
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- A natural-number version of `countBoolean` that counts the number of `true` values in a list. -/
def countBooleanNat (seq : List Bool) : Nat :=
  match seq with
  | [] => 0
  | hd :: tl => countBooleanNat tl + (if hd then 1 else 0)

@[simp] lemma countBooleanNat_nil : countBooleanNat [] = 0 := rfl

@[simp] lemma countBooleanNat_cons (b : Bool) (tl : List Bool) :
    countBooleanNat (b :: tl) = countBooleanNat tl + (if b then 1 else 0) := rfl

/-- Relates the integer-valued `countBoolean` to the natural-valued `countBooleanNat`. -/
lemma countBoolean_eq_coe_countBooleanNat (l : List Bool) :
    countBoolean l = (countBooleanNat l : Int) := by
  induction l with
  | nil =>
      simp [countBoolean, countBooleanNat]
  | cons b tl ih =>
      cases b <;> simp [countBoolean, countBooleanNat, ih]

/-- The count of `true` values is bounded by the list length. -/
lemma countBooleanNat_le_length (l : List Bool) :
    countBooleanNat l ≤ l.length := by
  induction l with
  | nil =>
      simp
  | cons b tl ih =>
      cases b with
      | false =>
          have h := ih.trans (Nat.le_succ _)
          simpa [countBooleanNat] using h
      | true =>
          have h := Nat.succ_le_succ ih
          simpa [countBooleanNat] using h

-- </vc-helpers>

-- <vc-definitions>
def countTrue (arr : Array Bool) (h_precond : countTrue_precond arr) : Nat :=
  countBooleanNat arr.toList
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def countTrue_postcond (arr : Array Bool) (count : Nat) (h_precond : countTrue_precond arr) : Prop :=
  0 ≤ count ∧ count ≤ arr.size ∧ countBoolean arr.toList = count

theorem countTrue_spec_satisfied (arr : Array Bool) (h_precond : countTrue_precond arr) :
    countTrue_postcond arr (countTrue arr h_precond) h_precond := by
  refine And.intro ?h0 ?hrest
  · exact Nat.zero_le _
  · refine And.intro ?h1 ?h2
    ·
      have hlen : countTrue arr h_precond ≤ arr.toList.length := by
        simpa [countTrue] using (countBooleanNat_le_length arr.toList)
      simpa using hlen
    ·
      have hco : countBoolean arr.toList = (countBooleanNat arr.toList : Int) :=
        countBoolean_eq_coe_countBooleanNat _
      simpa [countTrue] using hco
-- </vc-theorems>

/- Main function -/
