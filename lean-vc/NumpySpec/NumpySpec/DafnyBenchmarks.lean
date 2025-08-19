
/-!
# Dafny Numpy Specs (Stubs)

These stubs mirror the Dafny benchmark specifications in the `vericoding` repo
  (see <https://github.com/Beneficial-AI-Foundation/vericoding/tree/main/dafny/benchmarks/numpy_specs>).

For now they contain only *comments* describing the expected behaviour together
with Lean placeholders (`sorry`).  They compile, allowing the rest of the
`lake build` pipeline to succeed.

Each spec will later be replaced by a proper Lean definition plus a proof using
MPL (`Std.Do.Triple`).
-/

namespace NumpySpec.DafnyBenchmarks

/-!
Stub for `sum.dfy`

Dafny spec excerpt:

```dafny
method sum(a: array<int>) returns (s: int)
  ensures s == (* sum of elements in a *)
```
-/

def sum (a : List Int) : Int :=
  -- TODO: implement with fold once verified
  (a.foldl (· + ·) 0)

/-! Specification from `sum.dfy`: the result is the arithmetic sum of all
    elements.  Will be proved with MPL later. -/
theorem sum_spec (xs : List Int) : sum xs = xs.foldl (· + ·) 0 := by
  sorry

/-!
Stub for `prod.dfy`

```dafny
method prod(a: array<int>) returns (p: int)
  ensures p == (* product of elements in a *)
```
-/

def prod (a : List Int) : Int :=
  a.foldl (· * ·) 1

theorem prod_spec (xs : List Int) : prod xs = xs.foldl (· * ·) 1 := by
  sorry

end NumpySpec.DafnyBenchmarks

/-!
Below are additional placeholder stubs corresponding to other Dafny NumPy benchmarks.
They are *not* exhaustive yet (the original suite has about 43), but they
cover the most frequently-used operations so we can start linking Lean proofs
incrementally.  All come with a trivial specification lemma so the file
compiles while signalling the intended contract.
-/

namespace NumpySpec.DafnyBenchmarks

/-! Return the minimum of a non-empty list (`0` if empty, for now). -/
def listMin (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | x :: xs => (x :: xs).foldl (fun acc y => if y < acc then y else acc) x

theorem listMin_spec (xs : List Int) :
  (xs ≠ [] → ∃ m ∈ xs, (∀ y ∈ xs, m ≤ y) ∧ listMin xs = m) ∧ (xs = [] → listMin xs = 0) := by
  sorry

/-! Return the maximum of a non-empty list (`0` if empty). -/
def listMax (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | x :: xs => (x :: xs).foldl (fun acc y => if y > acc then y else acc) x

theorem listMax_spec (xs : List Int) :
  (xs ≠ [] → ∃ m ∈ xs, (∀ y ∈ xs, y ≤ m) ∧ listMax xs = m) ∧ (xs = [] → listMax xs = 0) := by
  sorry

/-! Compute the arithmetic mean as integer division. -/
def listMean (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | _  => (xs.foldl (· + ·) 0) / xs.length

theorem listMean_spec (xs : List Int) :
  xs ≠ [] → listMean xs * xs.length = xs.foldl (· + ·) 0 := by
  intro h
  -- proof to be supplied later
  sorry

/-! Dot product of two lists (truncates to shortest). -/
def dot (a b : List Int) : Int :=
  (List.zip a b).foldl (fun acc (p : Int × Int) => acc + p.fst * p.snd) 0

theorem dot_spec (a b : List Int) :

  dot a b = (List.zip a b).foldl (fun acc p => acc + p.fst * p.snd) 0 := by
  sorry

end NumpySpec.DafnyBenchmarks

/-!
## Additional placeholders (aligned with remaining Dafny specs)
-/

namespace NumpySpec.DafnyBenchmarks

/- Cumulative sum (prefix-scan). -/
def cumsum (xs : List Int) : List Int :=
  xs.foldl (fun (acc : List Int) x =>
              match acc with
              | [] => [x]
              | y :: _ => (x + y) :: acc) [] |>.reverse

theorem cumsum_spec (xs : List Int) : True := by
  trivial

/- Reverse a list. -/
def reverse (xs : List Int) : List Int := xs.reverse

theorem reverse_spec (xs : List Int) : reverse (reverse xs) = xs := by
  simp[reverse]

/- Concatenate two lists. -/
def concat (a b : List Int) : List Int := a ++ b

theorem concat_spec (a b : List Int) : concat a b = a ++ b := by
  rfl

/- Argmin: index of minimal element (0 if empty). -/
def argmin (xs : List Int) : Nat :=
  match xs with
  | [] => 0
  | x :: xs =>
      (List.foldl (fun (idxMin, curIdx, curMin) y => if y < curMin then (curIdx, curIdx+1, y) else (idxMin, curIdx+1, curMin)) (0,1,x) xs).1

/- TODO spec with existence — placeholder -/
theorem argmin_spec (xs : List Int) : True := by
  trivial

/- Argmax analogous -/
def argmax (xs : List Int) : Nat :=
  match xs with
  | [] => 0
  | x :: xs =>
      (List.foldl (fun (idxMax, curIdx, curMax) y => if y > curMax then (curIdx, curIdx+1, y) else (idxMax, curIdx+1, curMax)) (0,1,x) xs).1

theorem argmax_spec (xs : List Int) : True := by trivial

end NumpySpec.DafnyBenchmarks
