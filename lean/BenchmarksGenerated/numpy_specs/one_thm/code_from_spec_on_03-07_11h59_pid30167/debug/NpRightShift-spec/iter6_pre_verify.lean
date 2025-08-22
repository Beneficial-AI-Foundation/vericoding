namespace NpRightShift

def shiftRightInt (x : Int) (n : Nat) : Int :=
  if x ≥ 0 then
    Int.ofNat (x.natAbs >>> n)
  else
    -(Int.ofNat (((-x).natAbs - 1) >>> n + 1))

def rightShift {n : Nat} (a : Vector Int n) (b : Vector Nat n) 
  (h : ∀ i : Fin n, b[i] < 64) : Vector Int n := 
  Vector.ofFn (fun i => shiftRightInt (a[i]) (b[i]))

/- LLM HELPER -/
lemma Vector.ofFn_length {α : Type*} {n : Nat} (f : Fin n → α) : 
  (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, List.length_ofFn]

/- LLM HELPER -/
lemma Vector.ofFn_get {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn, Vector.get_mk]

theorem rightShift_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n) 
  (h : ∀ i : Fin n, b[i] < 64) :
  (rightShift a b h).toList.length = n ∧
  ∀ i : Fin n, (rightShift a b h)[i] = shiftRightInt (a[i]) (b[i]) := by
  constructor
  · simp [rightShift, Vector.ofFn_length]
  · intro i
    simp [rightShift, Vector.ofFn_get]

end NpRightShift