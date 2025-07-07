namespace NpRightShift

def shiftRightInt (x : Int) (n : Nat) : Int :=
  if x ≥ 0 then
    Int.ofNat (x.natAbs >>> n)
  else
    -(Int.ofNat (((-x).natAbs - 1) >>> n + 1))

def rightShift {n : Nat} (a : Vector Int n) (b : Vector Nat n) 
  (h : ∀ i : Fin n, b[i] < 64) : Vector Int n := 
  Vector.ofFn (fun i => shiftRightInt (a[i]) (b[i]))

-- LLM HELPER
lemma rightShift_get {n : Nat} (a : Vector Int n) (b : Vector Nat n) 
  (h : ∀ i : Fin n, b[i] < 64) (i : Fin n) :
  (rightShift a b h)[i] = shiftRightInt (a[i]) (b[i]) := by
  simp [rightShift]

theorem rightShift_spec {n : Nat} (a : Vector Int n) (b : Vector Nat n) 
  (h : ∀ i : Fin n, b[i] < 64) :
  (rightShift a b h).toList.length = n ∧
  ∀ i : Fin n, (rightShift a b h)[i] = shiftRightInt (a[i]) (b[i]) := by
  constructor
  · simp [rightShift]
  · intro i
    exact rightShift_get a b h i

end NpRightShift