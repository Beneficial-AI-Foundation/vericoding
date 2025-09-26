-- <vc-preamble>
@[reducible, simp]
def insert_precond (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) : Prop :=
  l ≤ oline.size ∧
  p ≤ nl.size ∧
  atPos ≤ l
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def insert (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) : Array Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def insert_postcond (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result: Array Char) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) :=
  result.size = l + p ∧
  (List.range p).all (fun i => result[atPos + i]! = nl[i]!) ∧
  (List.range atPos).all (fun i => result[i]! = oline[i]!) ∧
  (List.range (l - atPos)).all (fun i => result[atPos + p + i]! = oline[atPos + i]!)

theorem insert_spec_satisfied (oline: Array Char) (l: Nat) (nl: Array Char) (p: Nat) (atPos: Nat) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) :
    insert_postcond (oline) (l) (nl) (p) (atPos) (insert (oline) (l) (nl) (p) (atPos) h_precond) h_precond := by
  sorry
-- </vc-theorems>