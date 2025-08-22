/-
# NumPy IsClose Specification

Port of np_isclose.dfy to Lean 4
-/

namespace DafnySpecs.NpIsclose

/-- Check if elements are close within tolerance -/
def np_isclose {n : Nat} (a b : Vector Int n) (tol : Int) : Vector Bool n := 
  Vector.ofFn (fun i : Fin n => if -tol < a[i] - b[i] ∧ a[i] - b[i] < tol then true else false)

-- LLM HELPER
lemma vector_ofFn_length {n : Nat} (f : Fin n → Bool) : 
  (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, Vector.toList]

/-- Specification: The result has same length as inputs -/
theorem np_isclose_length {n : Nat} (a b : Vector Int n) (tol : Int)
  (h1 : n > 0)
  (h2 : tol > 0) :
  let ret := np_isclose a b tol
  ret.toList.length = n := by
  simp [np_isclose]
  exact vector_ofFn_length _

-- LLM HELPER
lemma vector_ofFn_get {n : Nat} (f : Fin n → Bool) (i : Fin n) :
  (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn, Vector.get]

/-- Specification: Closeness check -/
theorem np_isclose_spec {n : Nat} (a b : Vector Int n) (tol : Int)
  (h1 : n > 0)
  (h2 : tol > 0) :
  let ret := np_isclose a b tol
  ∀ i : Fin n, if -tol < a[i] - b[i] ∧ a[i] - b[i] < tol then ret[i] = true else ret[i] = false := by
  intro i
  simp [np_isclose]
  rw [vector_ofFn_get]
  by_cases h : -tol < a[i] - b[i] ∧ a[i] - b[i] < tol
  · simp [h]
  · simp [h]

end DafnySpecs.NpIsclose