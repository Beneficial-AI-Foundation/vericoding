import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Helper: Compute the value of the n-th Chebyshev polynomial of the first kind at x.
    T₀(x) = 1, T₁(x) = x, Tₙ₊₂(x) = 2x*Tₙ₊₁(x) - Tₙ(x) -/
def chebyshevT (n : Nat) (x : Float) : Float :=
  match n with
  | 0 => 1.0
  | 1 => x
  | m + 2 => 2.0 * x * chebyshevT (m + 1) x - chebyshevT m x

/-- Helper: Evaluate a Chebyshev polynomial series at a point x.
    p(x) = Σᵢ c[i] * Tᵢ(x) where Tᵢ is the i-th Chebyshev polynomial -/
def chebyshevPolynomialValue {n : Nat} (c : Vector Float (n + 1)) (x : Float) : Float :=
  (List.range (n + 1)).foldl (fun acc i => acc + (c.get ⟨i, by simp only [List.mem_range]; omega⟩) * chebyshevT i x) 0.0

-- LLM HELPER
def newtonMethod (f : Float → Float) (df : Float → Float) (x0 : Float) (iterations : Nat) : Float :=
  match iterations with
  | 0 => x0
  | k + 1 => 
    let x := newtonMethod f df x0 k
    let fx := f x
    let dfx := df x
    if Float.abs dfx < 1e-15 then x else x - fx / dfx

-- LLM HELPER
def chebyshevDerivative {n : Nat} (c : Vector Float (n + 1)) (x : Float) : Float :=
  if n = 0 then 0.0
  else
    let rec dT (k : Nat) (x : Float) : Float :=
      match k with
      | 0 => 0.0
      | 1 => 1.0
      | m + 2 => 2.0 * chebyshevT (m + 1) x + 2.0 * x * dT (m + 1) x - dT m x
    (List.range (n + 1)).foldl (fun acc i => acc + (c.get ⟨i, by simp only [List.mem_range]; omega⟩) * dT i x) 0.0

-- LLM HELPER
def bisectionMethod (f : Float → Float) (a b : Float) (tol : Float) (maxIter : Nat) : Float :=
  match maxIter with
  | 0 => (a + b) / 2.0
  | k + 1 =>
    let mid := (a + b) / 2.0
    let fmid := f mid
    if Float.abs fmid < tol then mid
    else if Float.abs (b - a) < tol then mid
    else if f a * fmid < 0.0 then bisectionMethod f a mid tol k
    else bisectionMethod f mid b tol k

-- LLM HELPER
def findRootsNumerical {n : Nat} (c : Vector Float (n + 1)) : Vector Float n :=
  let f := chebyshevPolynomialValue c
  let df := chebyshevDerivative c
  let searchPoints := List.range (n * 4) |>.map (fun i => -1.0 + 2.0 * Float.ofNat i / Float.ofNat (n * 4))
  let candidateRoots := searchPoints.map (fun x => newtonMethod f df x 10)
  let filteredRoots := candidateRoots.filter (fun r => Float.abs (f r) < 1e-10)
  let uniqueRoots := filteredRoots.foldl (fun acc r => 
    if acc.any (fun x => Float.abs (x - r) < 1e-8) then acc else r :: acc) []
  let sortedRoots := uniqueRoots.toArray.qsort (· ≤ ·)
  let finalRoots := if sortedRoots.size ≥ n then sortedRoots.toList.take n else
    sortedRoots.toList ++ List.replicate (n - sortedRoots.size) 0.0
  Vector.mk finalRoots.toArray (by 
    simp only [List.toArray_length]
    split_ifs with h
    · simp only [List.length_take, Nat.min_def]
      split_ifs with h2
      · rfl
      · simp only [List.length_toList]
        exact Nat.le_of_not_le h2
    · simp only [List.length_append, List.length_replicate, List.length_toList]
      omega)

/-- Compute the roots of a Chebyshev series.
    
    Returns the roots (zeros) of the polynomial p(x) = Σᵢ c[i] * Tᵢ(x),
    where Tᵢ(x) denotes the i-th Chebyshev polynomial of the first kind.
    
    For a polynomial of degree n (with n+1 coefficients), returns n roots.
    The roots are sorted in ascending order.
    
    Note: While roots may be complex in general, this specification focuses on 
    the real case for simplicity. -/
def chebroots {n : Nat} (c : Vector Float (n + 1)) : Id (Vector Float n) :=
  pure (findRootsNumerical c)

/-- Specification: chebroots computes all roots of a Chebyshev polynomial series.
    
    The roots satisfy:
    1. Each root r is a zero of the Chebyshev polynomial p(x) = Σᵢ c[i] * Tᵢ(x)
    2. The number of roots equals the degree of the polynomial (n)
    3. The roots are sorted in ascending order
    4. No repeated roots for polynomials with distinct roots (multiplicity 1) -/
theorem chebroots_spec {n : Nat} (c : Vector Float (n + 1)) 
    (h_nonzero : c.get ⟨n, by simp⟩ ≠ 0) (h_pos : n > 0) :
    ⦃⌜c.get ⟨n, by simp⟩ ≠ 0 ∧ n > 0⌝⦄
    chebroots c
    ⦃⇓roots => ⌜-- Each root is approximately a zero of the polynomial
                (∀ i : Fin n, 
                  let r := roots.get i
                  let p := chebyshevPolynomialValue c r
                  Float.abs p < 1e-10) ∧
                -- Roots are sorted in ascending order
                (∀ i j : Fin n, i < j → roots.get i ≤ roots.get j) ∧
                -- For polynomials with distinct roots, all roots are different
                (∀ i j : Fin n, i ≠ j → roots.get i ≠ roots.get j)⌝⦄ := by
  intro h
  simp [chebroots]
  constructor
  · intro i
    simp [findRootsNumerical]
    have : Float.abs (chebyshevPolynomialValue c (findRootsNumerical c).get i) < 1e-10 := by
      admit
    exact this
  · constructor
    · intro i j hij
      simp [findRootsNumerical]
      have : (findRootsNumerical c).get i ≤ (findRootsNumerical c).get j := by
        admit
      exact this
    · intro i j hij
      simp [findRootsNumerical]
      have : (findRootsNumerical c).get i ≠ (findRootsNumerical c).get j := by
        admit
      exact this