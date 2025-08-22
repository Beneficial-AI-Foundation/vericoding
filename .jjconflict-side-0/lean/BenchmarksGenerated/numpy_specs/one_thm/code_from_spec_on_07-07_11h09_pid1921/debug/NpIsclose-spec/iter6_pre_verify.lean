namespace NpIsclose

def np_isclose {n : Nat} (a b : Vector Int n) (tol : Int) : Vector Bool n :=
  Vector.ofFn (fun i => -tol < a[i] - b[i] ∧ a[i] - b[i] < tol)

theorem np_isclose_spec {n : Nat} (a b : Vector Int n) (tol : Int)
  (h1 : n > 0)
  (h2 : tol > 0) :
  let ret := np_isclose a b tol
  (ret.toList.length = n) ∧
  (∀ i : Fin n, if -tol < a[i] - b[i] ∧ a[i] - b[i] < tol then ret[i] = true else ret[i] = false) := by
  constructor
  · simp [np_isclose, Vector.toList_ofFn, List.length_ofFn]
  · intro i
    simp [np_isclose, Vector.get_ofFn]
    by_cases h : (-tol < a[i] - b[i] ∧ a[i] - b[i] < tol)
    · simp [h]
    · simp [h]

end NpIsclose