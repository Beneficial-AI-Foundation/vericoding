namespace NpBroadcast

def broadcast {n : Nat} (a : Vector Int n) (shape : Vector Int 2) : Matrix Int (shape[0]!) (shape[1]!) := 
  let rows := shape[0]!
  let cols := shape[1]!
  Matrix.of fun i j => 
    if rows = n then a[i]! else a[j]!

-- LLM HELPER
lemma matrix_toList_length {α : Type*} {m n : Nat} (M : Matrix α m n) : M.toList.length = m * n := by
  unfold Matrix.toList
  simp [List.length_join, List.sum_mapIdx]
  induction m with
  | zero => simp
  | succ m ih => 
    simp [List.range_succ, List.map_cons, List.sum_cons]
    rw [ih]
    ring

-- LLM HELPER
lemma matrix_get_spec {α : Type*} {m n : Nat} (M : Matrix α m n) (i : Nat) (j : Nat) 
  (hi : i < m) (hj : j < n) : M[i]![j]! = M i j := by
  simp [Matrix.get, List.get!]

theorem broadcast_spec {n : Nat} (a : Vector Int n) (shape : Vector Int 2)
  (h : shape[0]! = n ∨ shape[1]! = n) :
  let ret := broadcast a shape
  (ret.toList.length = shape[0]! * shape[1]!) ∧
  (∀ i j : Nat, i < shape[0]! → j < shape[1]! →
    if shape[0]! = n then ret[i]![j]! = a[i]! else ret[i]![j]! = a[j]!) := by
  constructor
  · -- First part: length property
    simp [broadcast]
    exact matrix_toList_length _
  · -- Second part: element property
    intros i j hi hj
    simp [broadcast]
    rw [matrix_get_spec]
    · simp [Matrix.of]
    · exact hi
    · exact hj

end NpBroadcast