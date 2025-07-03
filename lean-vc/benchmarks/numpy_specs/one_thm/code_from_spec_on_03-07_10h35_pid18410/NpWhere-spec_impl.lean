namespace NpWhere

def «where» {n : Nat} (condition : Vector Bool n) (x : Vector Int n) (y : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => if condition[i] then x[i] else y[i])

def whereWithTransform {n : Nat} (arr : Vector Int n) (condition : Int → Bool) (change : Int → Int) : Vector Int n := 
  Vector.ofFn (fun i => if condition (arr[i]) then change (arr[i]) else arr[i])

/- LLM HELPER -/
lemma Vector.ofFn_length {α : Type*} {n : Nat} (f : Fin n → α) : 
  (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn]

/- LLM HELPER -/
lemma Vector.ofFn_get {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) : 
  (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn]

theorem where_spec {n : Nat} (condition : Vector Bool n) (x : Vector Int n) (y : Vector Int n) :
  («where» condition x y).toList.length = n ∧
  (∀ i : Fin n, («where» condition x y)[i] = if condition[i] then x[i] else y[i]) ∧
  (∀ arr : Vector Int n, ∀ condition : Int → Bool, ∀ change : Int → Int,
    (whereWithTransform arr condition change).toList.length = n ∧
    ∀ i : Fin n, (whereWithTransform arr condition change)[i] = 
      if condition (arr[i]) then change (arr[i]) else arr[i]) := by
  constructor
  · -- Length property for where
    apply Vector.ofFn_length
  constructor
  · -- Correctness property for where
    intro i
    apply Vector.ofFn_get
  · -- Properties for whereWithTransform
    intro arr condition change
    constructor
    · -- Length property for whereWithTransform
      apply Vector.ofFn_length
    · -- Correctness property for whereWithTransform
      intro i
      apply Vector.ofFn_get

end NpWhere