import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma get_ofFn_apply {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f)[i] = f i := by
  simpa using Vector.get_ofFn f i

-- </vc-helpers>

-- <vc-definitions>
def np_isclose {n : Nat} (a b : Vector Int n) (tol : Int) : Vector Bool n :=
Vector.ofFn (fun i : Fin n => if h : (-tol < a[i] - b[i] ∧ a[i] - b[i] < tol) then true else false)
-- </vc-definitions>

-- <vc-theorems>
theorem np_isclose_spec {n : Nat} (a b : Vector Int n) (tol : Int)
  (h1 : n > 0)
  (h2 : tol > 0) :
  let ret := np_isclose a b tol
  (ret.toList.length = n) ∧
  (∀ i : Fin n, if -tol < a[i] - b[i] ∧ a[i] - b[i] < tol then ret[i] = true else ret[i] = false) :=
by
  let ret := np_isclose a b tol
  refine And.intro ?hlen ?hall
  · simpa using ret.2
  · intro i
    by_cases hcond : (-tol < a[i] - b[i] ∧ a[i] - b[i] < tol)
    · simp [ret, np_isclose, get_ofFn_apply, hcond]
    · simp [ret, np_isclose, get_ofFn_apply, hcond]

-- </vc-theorems>
