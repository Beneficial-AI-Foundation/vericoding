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
  simp [Vector.ofFn]

/- LLM HELPER -/
lemma Vector.get_ofFn {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) : 
  (Vector.ofFn f)[i] = f i := by
  simp [Vector.ofFn]

theorem rightShift_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n) 
  (h : ∀ i : Fin n, b[i] < 64) :
  (rightShift a b h).toList.length = n ∧
  ∀ i : Fin n, (rightShift a b h)[i] = shiftRightInt (a[i]) (b[i]) := by
  constructor
  · simp [rightShift, Vector.ofFn]
  · intro i
    simp [rightShift, Vector.get_ofFn]

end NpRightShift