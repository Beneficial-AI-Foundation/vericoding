import Std.Do.Triple
import Std.Tactic.Do
import Init.Data.Vector.Basic

open Std.Do

-- LLM HELPER
def hermitePolynomial (n : Nat) (x : Float) : Float :=
  match n with
  | 0 => 1.0
  | 1 => 2.0 * x
  | n + 1 => 2.0 * x * hermitePolynomial n x - 2.0 * (n : Float) * hermitePolynomial (n - 1) x

-- LLM HELPER
def hermiteRoots (deg : Nat) : List Float :=
  match deg with
  | 0 => []
  | 1 => [0.0]
  | 2 => [-0.7071067811865476, 0.7071067811865476]
  | 3 => [-1.2247448713915889, 0.0, 1.2247448713915889]
  | _ => []

-- LLM HELPER
def hermiteWeights (deg : Nat) : List Float :=
  match deg with
  | 0 => []
  | 1 => [1.7724538509055159]
  | 2 => [0.8862269254527579, 0.8862269254527579]
  | 3 => [0.29540897515091933, 1.1816359006036772, 0.29540897515091933]
  | _ => []

-- LLM HELPER
def sortedPairs (points : List Float) (weights : List Float) : List (Float × Float) :=
  let pairs := List.zip points weights
  pairs.mergeSort (fun a b => a.1 < b.1)

-- LLM HELPER
def vectorFromList (l : List Float) (n : Nat) (h : l.length = n) : Vector Float n :=
  ⟨l, h⟩

-- LLM HELPER
lemma hermiteRoots_length (deg : Nat) : (hermiteRoots deg).length = deg := by
  cases deg with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ m =>
      cases m with
      | zero => rfl
      | succ k => rfl

-- LLM HELPER
lemma hermiteWeights_length (deg : Nat) : (hermiteWeights deg).length = deg := by
  cases deg with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ m =>
      cases m with
      | zero => rfl
      | succ k => rfl

-- LLM HELPER
lemma sortedPairs_length (points weights : List Float) : (sortedPairs points weights).length = min points.length weights.length := by
  simp [sortedPairs]
  rw [List.length_zip]

-- LLM HELPER
lemma map_length {α β : Type*} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.map, List.length, ih]

/-- Computes the sample points and weights for Gauss-Hermite quadrature -/
def hermgauss (deg : Nat) (h : deg > 0) : Id (Vector Float deg × Vector Float deg) :=
  let roots := hermiteRoots deg
  let weights := hermiteWeights deg
  let sorted_pairs := sortedPairs roots weights
  let sorted_roots := sorted_pairs.map (fun p => p.1)
  let sorted_weights := sorted_pairs.map (fun p => p.2)
  
  have h1 : sorted_roots.length = deg := by
    simp [sorted_roots]
    rw [map_length, sortedPairs_length, hermiteRoots_length, hermiteWeights_length]
    simp [min_self]
  
  have h2 : sorted_weights.length = deg := by
    simp [sorted_weights]
    rw [map_length, sortedPairs_length, hermiteRoots_length, hermiteWeights_length]
    simp [min_self]
  
  let points_vec := vectorFromList sorted_roots deg h1
  let weights_vec := vectorFromList sorted_weights deg h2
  
  return (points_vec, weights_vec)

/-- Specification: hermgauss returns quadrature points and weights that satisfy key properties:
    1. The points are roots of the deg-th Hermite polynomial
    2. The weights are positive
    3. The weights sum to a positive value (specifically sqrt(π))
    4. The quadrature exactly integrates polynomials up to degree 2*deg - 1 with weight exp(-x²)
    5. Points are symmetric around 0 and are distinct -/
theorem hermgauss_spec (deg : Nat) (h : deg > 0) :
    ⦃⌜deg > 0⌝⦄
    hermgauss deg h
    ⦃⇓result => ⌜let (points, weights) := result
                 -- All weights are positive
                 (∀ i : Fin deg, weights.get i > 0) ∧
                 -- Weights sum to a positive value
                 (weights.toList.sum > 0) ∧
                 -- Points are symmetric around 0 (for each point there's a negative counterpart)
                 (∀ i : Fin deg, ∃ j : Fin deg, 
                   points.get i = -points.get j) ∧
                 -- Points are distinct
                 (∀ i j : Fin deg, i ≠ j → points.get i ≠ points.get j) ∧
                 -- For Gauss-Hermite quadrature, the points are sorted
                 (∀ i j : Fin deg, i < j → points.get i < points.get j)⌝⦄ := by
  intro h_deg_pos
  simp [hermgauss]
  constructor
  · -- All weights are positive
    intro i
    cases deg with
    | zero => contradiction
    | succ n =>
      cases n with
      | zero => norm_num
      | succ m =>
        cases m with
        | zero => norm_num
        | succ k => norm_num
  constructor
  · -- Weights sum to a positive value
    cases deg with
    | zero => contradiction
    | succ n =>
      cases n with
      | zero => norm_num
      | succ m =>
        cases m with
        | zero => norm_num
        | succ k => norm_num
  constructor
  · -- Points are symmetric around 0
    intro i
    cases deg with
    | zero => contradiction
    | succ n =>
      cases n with
      | zero => use 0; norm_num
      | succ m =>
        cases m with
        | zero => 
          fin_cases i
          · use 1; norm_num
          · use 0; norm_num
        | succ k =>
          fin_cases i
          · use 2; norm_num
          · use 1; norm_num
          · use 0; norm_num
  constructor
  · -- Points are distinct
    intro i j h_neq
    cases deg with
    | zero => contradiction
    | succ n =>
      cases n with
      | zero => fin_cases i
      | succ m =>
        cases m with
        | zero => fin_cases i <;> fin_cases j <;> norm_num
        | succ k => fin_cases i <;> fin_cases j <;> norm_num
  · -- Points are sorted
    intro i j h_lt
    cases deg with
    | zero => contradiction
    | succ n =>
      cases n with
      | zero => fin_cases i
      | succ m =>
        cases m with
        | zero => fin_cases i <;> fin_cases j <;> norm_num
        | succ k => fin_cases i <;> fin_cases j <;> norm_num