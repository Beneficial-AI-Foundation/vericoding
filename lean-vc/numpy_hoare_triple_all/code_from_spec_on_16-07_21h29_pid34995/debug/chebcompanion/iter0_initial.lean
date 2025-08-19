import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.polynomial.chebyshev.chebcompanion: Return the scaled companion matrix of c.

    The basis polynomials are scaled so that the companion matrix is
    symmetric when c is a Chebyshev basis polynomial. This provides
    better eigenvalue estimates than the unscaled case and for basis
    polynomials the eigenvalues are guaranteed to be real if
    numpy.linalg.eigvalsh is used to obtain them.

    Parameters:
    - c : 1-D array of Chebyshev series coefficients ordered from low to high degree

    Returns:
    - mat : Scaled companion matrix of dimensions (deg, deg) where deg = len(c) - 1
-/
def chebcompanion {n : Nat} (c : Vector Float (n + 2)) : Id (Vector (Vector Float (n + 1)) (n + 1)) :=
  Id.pure <| Vector.ofFn fun i : Fin (n + 1) => 
    Vector.ofFn fun j : Fin (n + 1) => 
      if j.val = i.val + 1 then
        -- Superdiagonal
        if i.val = 0 then Float.sqrt 0.5 else 0.5
      else if i.val = j.val + 1 then
        -- Subdiagonal
        if j.val = 0 then Float.sqrt 0.5 else 0.5
      else if j.val = n then
        -- Last column
        let adjustment := (c.get i.castSucc / c[Fin.last (n + 1)]?) * 0.5
        if i.val < n then
          (if i = 0 then -Float.sqrt 0.5 else -0.5) - adjustment
        else -adjustment
      else
        -- Main diagonal and other elements
        0.0

/-- Specification: chebcompanion returns a scaled companion matrix with specific structure.

    Precondition: The input vector has at least 2 elements (enforced by type)
    
    Postcondition: The result is an (n+1) × (n+1) matrix where:
    1. The superdiagonal and subdiagonal have specific values (0.5 for most entries, sqrt(0.5) for the first)
    2. The last column is adjusted by scaled coefficients
    3. The matrix structure ensures symmetry for Chebyshev basis polynomials
-/
theorem chebcompanion_spec {n : Nat} (c : Vector Float (n + 2)) :
    ⦃⌜True⌝⦄
    chebcompanion c
    ⦃⇓mat => ⌜-- The resulting matrix has specific structure for Chebyshev companion matrices
              -- Superdiagonal elements (above main diagonal)
              (∀ i : Fin n, (mat.get i.castSucc).get i.succ = 0.5) ∧
              -- Special case for first superdiagonal element
              (n > 0 → (mat.get 0).get 1 = Float.sqrt 0.5) ∧
              -- Subdiagonal elements (below main diagonal)  
              (∀ i : Fin n, (mat.get i.succ).get i.castSucc = 0.5) ∧
              -- Special case for first subdiagonal element
              (n > 0 → (mat.get 1).get 0 = Float.sqrt 0.5) ∧
              -- Last column contains scaled coefficient ratios
              (∀ i : Fin (n + 1), 
                ∃ adjustment : Float,
                adjustment = (c.get i.castSucc / c[Fin.last (n + 1)]?) * 0.5 ∧
                (mat.get i).get (Fin.last n) = 
                  (if h : i.val < n then
                     (if i = 0 then -Float.sqrt 0.5 else -0.5) - adjustment
                   else -adjustment))⌝⦄ := by
  simp [chebcompanion]
  simp [HoareLogic.entails]
  intros
  constructor
  · -- Superdiagonal elements
    intro i
    simp [Vector.get, Vector.ofFn]
    have h1 : i.castSucc.val = i.val := by simp [Fin.castSucc]
    have h2 : i.succ.val = i.val + 1 := by simp [Fin.succ]
    have h3 : i.succ.val = i.castSucc.val + 1 := by simp [h1, h2]
    simp [h3]
    split_ifs with h
    · simp at h
      cases h
      exact rfl
    · exact rfl
  constructor
  · -- Special case for first superdiagonal element
    intro hn
    simp [Vector.get, Vector.ofFn]
    simp [Fin.castSucc, Fin.succ]
    exact rfl
  constructor
  · -- Subdiagonal elements
    intro i
    simp [Vector.get, Vector.ofFn]
    have h1 : i.succ.val = i.val + 1 := by simp [Fin.succ]
    have h2 : i.castSucc.val = i.val := by simp [Fin.castSucc]
    have h3 : i.succ.val = i.castSucc.val + 1 := by simp [h1, h2]
    simp [h3]
    split_ifs with h
    · simp at h
      cases h
      exact rfl
    · exact rfl
  constructor
  · -- Special case for first subdiagonal element
    intro hn
    simp [Vector.get, Vector.ofFn]
    simp [Fin.succ, Fin.castSucc]
    exact rfl
  · -- Last column
    intro i
    simp [Vector.get, Vector.ofFn]
    exists (c.get i.castSucc / c[Fin.last (n + 1)]?) * 0.5
    constructor
    · rfl
    · simp [Fin.last]
      split_ifs with h
      · simp
        split_ifs with h2
        · simp
        · simp
      · simp