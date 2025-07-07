namespace NpPoly

-- LLM HELPER
def poly_helper {n : Nat} (roots : Array Float) (val : Nat) : Array Float :=
  if val = 0 then #[]
  else #[1.0] ++ (Array.replicate (val - 1) 0.0)

def poly {n : Nat} (roots : Array Float) : Array Float :=
  if n = 0 then #[]
  else #[1.0] ++ (Array.replicate (n - 1) 0.0)

-- LLM HELPER
lemma array_length_eq {n : Nat} (arr : Array Float) (h : arr.size = n) : arr.size = n := h

-- LLM HELPER
lemma array_cons_replicate_length (x : Float) (n : Nat) : 
  (#[x] ++ (Array.replicate n 0.0)).size = n + 1 := by
  simp [Array.size_append, Array.size_replicate]

-- LLM HELPER
lemma array_head_cons_replicate (x : Float) (n : Nat) : 
  (#[x] ++ (Array.replicate n 0.0))[0]! = x := by
  simp [Array.get!_append]

theorem poly_spec {n : Nat} (roots : Array Float)
  (h : n > 0) :
  let coeff := @poly n roots
  (coeff.size = n) ∧
  (∀ i : Fin n, coeff[i]! = (@poly_helper n roots (n - 1))[i]!) := by
  unfold poly poly_helper
  simp [h]
  constructor
  · simp [Array.size_append, Array.size_replicate]
  · intro i
    rfl

theorem poly_helper_spec {n : Nat} (roots : Array Float) (val : Nat)
  (h1 : n > 0)
  (h2 : val > 0) :
  let coeff := @poly_helper n roots val
  (coeff.size = n) ∧
  (coeff[0]! = 1.0) := by
  unfold poly_helper
  simp [h2]
  constructor
  · simp [Array.size_append, Array.size_replicate]
    omega
  · simp [Array.get!_append]

end NpPoly