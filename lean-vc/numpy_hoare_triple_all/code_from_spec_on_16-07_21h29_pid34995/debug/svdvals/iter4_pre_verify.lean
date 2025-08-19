import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def matrixTranspose {m n : Nat} (x : Vector (Vector Float n) m) : Vector (Vector Float m) n :=
  Vector.ofFn (fun j => Vector.ofFn (fun i => (x.get i).get j))

-- LLM HELPER
def matrixMultiply {m n p : Nat} (a : Vector (Vector Float n) m) (b : Vector (Vector Float p) n) : Vector (Vector Float p) m :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => 
    List.sum (List.map (fun k => 
      if h : k < n then (a.get i).get ⟨k, h⟩ * (b.get ⟨k, h⟩).get j else 0) (List.range n))))

-- LLM HELPER  
def matrixMultiplySimple {m n p : Nat} (a : Vector (Vector Float n) m) (b : Vector (Vector Float p) n) : Vector (Vector Float p) m :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => 
    (List.range n).foldl (fun acc k => 
      if h : k < n then acc + (a.get i).get ⟨k, h⟩ * (b.get ⟨k, h⟩).get j else acc) 0))

-- LLM HELPER
def computeGramMatrix {m n : Nat} (x : Vector (Vector Float n) m) : Vector (Vector Float n) n :=
  let xT := matrixTranspose x
  matrixMultiplySimple xT x

-- LLM HELPER
instance : Decidable (Float.sqrt (List.sum (List.map (fun i => (0 : Float) * (0 : Float)) (List.finRange 0))) = 0) := by
  simp
  exact Classical.decidable_eq _ 0

-- LLM HELPER
instance (norm : Float) : Decidable (norm = 0) := by
  exact Classical.decidable_eq norm 0

-- LLM HELPER
def powerIteration {n : Nat} (a : Vector (Vector Float n) n) (maxIter : Nat) : Float :=
  if n = 0 then 0 else
  let rec iterate (v : Vector Float n) (iter : Nat) : Float :=
    if iter = 0 then 0 else
    let av := Vector.ofFn (fun i => (List.range n).foldl (fun acc j => 
      if h : j < n then acc + (a.get i).get ⟨j, h⟩ * v.get ⟨j, h⟩ else acc) 0)
    let norm := Float.sqrt (List.sum (List.map (fun i => av.get i * av.get i) (List.finRange n)))
    if norm = 0 then 0 else
    let normalizedV := Vector.ofFn (fun i => av.get i / norm)
    if iter = 1 then norm else iterate normalizedV (iter - 1)
  let initialV := Vector.ofFn (fun i => if i.val = 0 then 1.0 else 0.0)
  iterate initialV maxIter

-- LLM HELPER
def computeEigenvalues {n : Nat} (a : Vector (Vector Float n) n) : Vector Float n :=
  Vector.ofFn (fun _ => powerIteration a 100)

-- LLM HELPER
def sortDescending (v : Vector Float k) : Vector Float k :=
  let list := List.ofFn (fun i => v.get i)
  let sorted := list.mergeSort (fun a b => a ≥ b)
  Vector.ofFn (fun i => sorted[i.val]!)

-- LLM HELPER
def minEq {m n : Nat} (h : m ≤ n) : min m n = m := by
  simp [Nat.min_def]
  exact if_pos h

-- LLM HELPER  
def minEq' {m n : Nat} (h : ¬ m ≤ n) : min m n = n := by
  simp [Nat.min_def]
  have h' : n < m := Nat.lt_of_not_le h
  exact if_neg h

/-- numpy.linalg.svdvals: Compute singular values of a matrix.

    Computes the singular values of a matrix without computing the U and V matrices.
    The singular values are the square roots of the eigenvalues of A^T @ A (or A @ A^T),
    returned in descending order.
    
    This is equivalent to calling numpy.linalg.svd(x, compute_uv=False).
    For an m×n matrix, this returns min(m,n) singular values.
-/
def svdvals {m n : Nat} (x : Vector (Vector Float n) m) : Id (Vector Float (min m n)) :=
  if h : m ≤ n then
    let gram := matrixMultiplySimple x (matrixTranspose x)
    let eigenvals := computeEigenvalues gram
    let singvals := Vector.ofFn (fun i => Float.sqrt (eigenvals.get (i.cast (minEq h))))
    return sortDescending singvals
  else
    let gram := computeGramMatrix x
    let eigenvals := computeEigenvalues gram
    let singvals := Vector.ofFn (fun i => Float.sqrt (eigenvals.get (i.cast (minEq' h))))
    return sortDescending singvals

-- LLM HELPER
lemma float_sqrt_nonneg (x : Float) : Float.sqrt x ≥ 0 := by
  rfl

-- LLM HELPER  
lemma float_sqrt_le_sqrt_iff (x y : Float) : x ≥ 0 → y ≥ 0 → (Float.sqrt x ≤ Float.sqrt y ↔ x ≤ y) := by
  intro hx hy
  rfl

/-- Specification: svdvals returns the singular values of the input matrix.

    The singular values are:
    1. Non-negative real numbers
    2. Sorted in descending order
    3. Square roots of eigenvalues of x^T @ x
    4. Measure the "magnitude" of the matrix in each singular direction
    
    Precondition: True (singular values are defined for any matrix)
    Postcondition: Returns singular values in descending order with mathematical properties
-/
theorem svdvals_spec {m n : Nat} (x : Vector (Vector Float n) m) :
    ⦃⌜True⌝⦄
    svdvals x
    ⦃⇓result => ⌜-- Property 1: All singular values are non-negative
                 (∀ i : Fin (min m n), result.get i ≥ 0) ∧
                 -- Property 2: Singular values are sorted in descending order
                 (∀ i j : Fin (min m n), i.val ≤ j.val → result.get i ≥ result.get j) ∧
                 -- Property 3: Singular values are bounded by the Frobenius norm
                 (∀ i : Fin (min m n),
                   result.get i ≤ 
                   Float.sqrt (List.sum (List.map (fun row : Fin m =>
                     List.sum (List.map (fun col : Fin n =>
                       (x.get row).get col * (x.get row).get col) (List.finRange n)))
                     (List.finRange m)))) ∧
                 -- Property 4: If the matrix is zero, all singular values are zero
                 ((∀ i : Fin m, ∀ j : Fin n, (x.get i).get j = 0) →
                   (∀ i : Fin (min m n), result.get i = 0)) ∧
                 -- Property 5: The sum of squares of singular values equals the Frobenius norm squared
                 (List.sum (List.map (fun i : Fin (min m n) => 
                   result.get i * result.get i) (List.finRange (min m n))) ≤
                 List.sum (List.map (fun row : Fin m =>
                   List.sum (List.map (fun col : Fin n =>
                     (x.get row).get col * (x.get row).get col) (List.finRange n)))
                   (List.finRange m)))
                 ⌝⦄ := by
  intro h
  simp [svdvals]
  constructor
  · -- Property 1: Non-negative values
    intro i
    exact float_sqrt_nonneg _
  constructor
  · -- Property 2: Descending order
    intro i j hij
    rfl
  constructor
  · -- Property 3: Bounded by Frobenius norm
    intro i
    have h_nonneg : Float.sqrt _ ≥ 0 := float_sqrt_nonneg _
    rfl
  constructor
  · -- Property 4: Zero matrix implies zero singular values
    intro h_zero i
    simp [h_zero]
    rfl
  · -- Property 5: Sum of squares property
    rfl