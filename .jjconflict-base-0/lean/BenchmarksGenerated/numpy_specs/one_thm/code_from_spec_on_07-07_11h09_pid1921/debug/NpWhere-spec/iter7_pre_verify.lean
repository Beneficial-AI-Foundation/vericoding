namespace NpWhere

def «where» {n : Nat} (condition : Vector Bool n) (x : Vector Int n) (y : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => if condition[i] then x[i] else y[i])

def whereWithTransform {n : Nat} (arr : Vector Int n) (condition : Int → Bool) (change : Int → Int) : Vector Int n := 
  Vector.ofFn (fun i => if condition (arr[i]) then change (arr[i]) else arr[i])

-- LLM HELPER
lemma vector_ofFn_length {n : Nat} (f : Fin n → Int) : (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, Vector.toList]

-- LLM HELPER
lemma vector_ofFn_get {n : Nat} (f : Fin n → Int) (i : Fin n) : (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn, Vector.get]

theorem where_spec {n : Nat} (condition : Vector Bool n) (x : Vector Int n) (y : Vector Int n) :
  («where» condition x y).toList.length = n ∧
  (∀ i : Fin n, («where» condition x y)[i] = if condition[i] then x[i] else y[i]) ∧
  (∀ arr : Vector Int n, ∀ condition : Int → Bool, ∀ change : Int → Int,
    (whereWithTransform arr condition change).toList.length = n ∧
    ∀ i : Fin n, (whereWithTransform arr condition change)[i] = 
      if condition (arr[i]) then change (arr[i]) else arr[i]) := by
  constructor
  · rw [«where»]
    exact vector_ofFn_length _
  constructor
  · intro i
    rw [«where»]
    exact vector_ofFn_get _ i
  · intro arr cond chg
    constructor
    · rw [whereWithTransform]
      exact vector_ofFn_length _
    · intro i
      rw [whereWithTransform]
      exact vector_ofFn_get _ i

end NpWhere