-- <vc-preamble>
@[reducible]
def moveZeroes_precond (xs : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- Count how many times a specific value appears in the list
-- </vc-helpers>

-- <vc-definitions>
def moveZeroes (xs : List Int) (h_precond : moveZeroes_precond (xs)) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def countVal (val : Int) : List Int → Nat
  | [] => 0
  | x :: xs =>
    let rest := countVal val xs
    if x = val then rest + 1 else rest

-- Check whether one list is a subsequence of another (preserving relative order)
def isSubsequence (xs ys : List Int) : Bool :=
  match xs, ys with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xt, y :: yt =>
    if x = y then isSubsequence xt yt else isSubsequence xs yt
@[reducible]
def moveZeroes_postcond (xs : List Int) (result: List Int) (h_precond : moveZeroes_precond (xs)) : Prop :=
  -- 1. All non-zero elements must maintain their relative order
  isSubsequence (xs.filter (fun x => x ≠ 0)) result = true ∧

  -- 2. All zeroes must be located at the end of the output list
  (result.dropWhile (fun x => x ≠ 0)).all (fun x => x = 0) ∧

  -- 3. The output must contain the same number of elements,
  --    and the number of zeroes must remain unchanged
  countVal 0 xs = countVal 0 result ∧
  xs.length = result.length

theorem moveZeroes_spec_satisfied (xs: List Int) (h_precond : moveZeroes_precond (xs)) :
    moveZeroes_postcond (xs) (moveZeroes (xs) h_precond) h_precond := by
  sorry
-- </vc-theorems>