/-
# NumPy Where Specification

Port of np_where.dfy to Lean 4
-/

namespace DafnySpecs.NpWhere

/-- Return elements chosen from x or y depending on condition -/
def «where» {n : Nat} (condition : Vector Bool n) (x : Vector Int n) (y : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => if condition[i] then x[i] else y[i])

/-- Specification: The result has the same length as inputs -/
theorem where_length {n : Nat} (condition : Vector Bool n) (x : Vector Int n) (y : Vector Int n) :
  («where» condition x y).toList.length = n := by
  simp [«where»]

/-- Specification: Each element is chosen from x or y based on condition -/
theorem where_spec {n : Nat} (condition : Vector Bool n) (x : Vector Int n) (y : Vector Int n) :
  ∀ i : Fin n, («where» condition x y)[i] = if condition[i] then x[i] else y[i] := by
  intro i
  simp [«where»]

/-- Alternative version with predicate and transformation function (from Dafny) -/
def whereWithTransform {n : Nat} (arr : Vector Int n) (condition : Int → Bool) (change : Int → Int) : Vector Int n := 
  Vector.ofFn (fun i => if condition (arr[i]) then change (arr[i]) else arr[i])

/-- Specification: Result has same length as input -/
theorem whereWithTransform_length {n : Nat} (arr : Vector Int n) (condition : Int → Bool) (change : Int → Int) :
  (whereWithTransform arr condition change).toList.length = n := by
  simp [whereWithTransform]

/-- Specification: Elements are transformed based on condition -/
theorem whereWithTransform_spec {n : Nat} (arr : Vector Int n) (condition : Int → Bool) (change : Int → Int) :
  ∀ i : Fin n, (whereWithTransform arr condition change)[i] = 
    if condition (arr[i]) then change (arr[i]) else arr[i] := by
  intro i
  simp [whereWithTransform]

end DafnySpecs.NpWhere