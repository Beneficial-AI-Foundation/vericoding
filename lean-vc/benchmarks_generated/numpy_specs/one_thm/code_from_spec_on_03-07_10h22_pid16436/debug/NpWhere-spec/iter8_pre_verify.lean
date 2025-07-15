namespace NpWhere

def «where» {n : Nat} (condition : Vector Bool n) (x : Vector Int n) (y : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => if condition[i] then x[i] else y[i])

def whereWithTransform {n : Nat} (arr : Vector Int n) (condition : Int → Bool) (change : Int → Int) : Vector Int n := 
  Vector.ofFn (fun i => if condition (arr[i]) then change (arr[i]) else arr[i])

/-- LLM HELPER -/
lemma vector_ofFn_length {n : Nat} (f : Fin n → Int) : (Vector.ofFn f).toList.length = n := by
  rw [Vector.toList_ofFn]
  simp

/-- LLM HELPER -/
lemma vector_ofFn_get {n : Nat} (f : Fin n → Int) (i : Fin n) : (Vector.ofFn f)[i] = f i := by
  rw [Vector.get_ofFn]

theorem where_spec {n : Nat} (condition : Vector Bool n) (x : Vector Int n) (y : Vector Int n) :
  («where» condition x y).toList.length = n ∧
  (∀ i : Fin n, («where» condition x y)[i] = if condition[i] then x[i] else y[i]) ∧
  (∀ arr : Vector Int n, ∀ condition : Int → Bool, ∀ change : Int → Int,
    (whereWithTransform arr condition change).toList.length = n ∧
    ∀ i : Fin n, (whereWithTransform arr condition change)[i] = 
      if condition (arr[i]) then change (arr[i]) else arr[i]) := by
  constructor
  · unfold «where»
    exact vector_ofFn_length _
  constructor
  · intro i
    unfold «where»
    exact vector_ofFn_get _ i
  · intro arr condition_fn change
    constructor
    · unfold whereWithTransform
      exact vector_ofFn_length _
    · intro i
      unfold whereWithTransform
      exact vector_ofFn_get _ i

end NpWhere