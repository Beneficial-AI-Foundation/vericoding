import Mathlib
-- <vc-preamble>
@[reducible, simp]
def intersperse_precond (numbers : Array Int) (delim : Int) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def intersperse (numbers : Array Int) (delim : Int) (h_precond : intersperse_precond numbers delim) : Array Int :=
  let n := numbers.size
if h0 : n = 0 then
  #[]
else
  let len := 2 * n - 1
  Array.ofFn (fun j : Fin len =>
    if j.1 % 2 = 0 then numbers[j.1 / 2]! else delim)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def intersperse_postcond (numbers : Array Int) (delim : Int) (res: Array Int) (h_precond : intersperse_precond numbers delim) : Prop :=
  (numbers.size = 0 → res.size = 0) ∧
  (numbers.size ≠ 0 → res.size = 2 * numbers.size - 1) ∧
  (∀ i, 0 ≤ i ∧ i < res.size ∧ i % 2 = 0 → res[i]! = numbers[i / 2]!) ∧
  (∀ i, 0 ≤ i ∧ i < res.size ∧ i % 2 = 1 → res[i]! = delim)

theorem intersperse_spec_satisfied (numbers: Array Int) (delim: Int) (h_precond : intersperse_precond numbers delim) :
    intersperse_postcond numbers delim (intersperse numbers delim h_precond) h_precond := by
  classical
let n := numbers.size
refine And.intro ?h0 (And.intro ?h1 (And.intro ?h2 ?h3))
· intro hz
  have hn : n = 0 := by simpa [n] using hz
  simp [intersperse, n, hn]
· intro hzne
  have hn : n ≠ 0 := by simpa [n] using hzne
  simp [intersperse, n, hn]
· intro i hi
  have _h0 : 0 ≤ i := And.left hi
  have hi' := And.right hi
  have hiltsize : i < (intersperse numbers delim h_precond).size := And.left hi'
  have hmod : i % 2 = 0 := And.right hi'
  by_cases hn : n = 0
  · have : i < 0 := by simpa [intersperse, n, hn] using hiltsize
    exact (Nat.not_lt_zero i this).elim
  · have hlt : i < 2 * n - 1 := by simpa [intersperse, n, hn] using hiltsize
    simpa [intersperse, n, hn, Array.get!, hlt, hmod]
· intro i hi
  have _h0 : 0 ≤ i := And.left hi
  have hi' := And.right hi
  have hiltsize : i < (intersperse numbers delim h_precond).size := And.left hi'
  have hmod1 : i % 2 = 1 := And.right hi'
  by_cases hn : n = 0
  · have : i < 0 := by simpa [intersperse, n, hn] using hiltsize
    exact (Nat.not_lt_zero i this).elim
  · have hlt : i < 2 * n - 1 := by simpa [intersperse, n, hn] using hiltsize
    have hne : i % 2 ≠ 0 := by
      intro hzero
      simpa [hzero] using hmod1
    simpa [intersperse, n, hn, Array.get!, hlt, hne]
-- </vc-theorems>
