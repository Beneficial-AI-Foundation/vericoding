import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Complex number type for FFT operations -/
structure Complex where
  /-- Real part of the complex number -/
  re : Float
  /-- Imaginary part of the complex number -/
  im : Float

/-- Helper function to check if a vector is Hermitian-symmetric -/
def isHermitianSymmetric {n : Nat} (a : Vector Complex n) : Prop :=
  ∀ i : Fin n, ∀ j : Fin n, (i.val + j.val = n - 1) → 
    (a.get i).re = (a.get j).re ∧ (a.get i).im = -(a.get j).im

-- LLM HELPER
def expandHermitianSymmetric {k : Nat} (a : Vector Complex k) (n : Nat) : Vector Complex n :=
  Vector.ofFn (fun i : Fin n => 
    if h : i.val < k then 
      a.get ⟨i.val, h⟩
    else
      let mirror_idx := n - i.val
      if h' : mirror_idx < k then
        let original := a.get ⟨mirror_idx, h'⟩
        ⟨original.re, -original.im⟩
      else
        ⟨0, 0⟩)

-- LLM HELPER
def complexToReal (c : Complex) : Float := c.re

-- LLM HELPER
def Float.pi : Float := 3.14159265358979323846

-- LLM HELPER
def inverseFFTStep {n : Nat} (expanded : Vector Complex n) : Vector Float n :=
  Vector.ofFn (fun i : Fin n => 
    let sum := (List.range n).foldl (fun acc j => 
      let angle := 2 * Float.pi * i.val.toFloat * j.toFloat / n.toFloat
      let cos_val := Float.cos angle
      let sin_val := Float.sin angle
      let c := expanded.get ⟨j, by 
        have : j < n := by
          rw [List.mem_range] at *
          exact Nat.lt_of_mem_range (List.mem_range.mpr rfl)
        exact this⟩
      acc + c.re * cos_val + c.im * sin_val) 0
    sum / n.toFloat)

/-- Computes the inverse of rfft (real-valued inverse FFT) -/
def irfft {k : Nat} (a : Vector Complex k) (n : Nat) : Id (Vector Float n) :=
  pure (
    let expanded := expandHermitianSymmetric a n
    inverseFFTStep expanded
  )

/-- Specification: irfft computes the inverse of rfft with proper length restoration -/
theorem irfft_spec {k : Nat} (a : Vector Complex k) (n : Nat) 
    (h_length : n = 2 * (k - 1)) 
    (h_hermitian : isHermitianSymmetric a) 
    (h_nonempty : k > 0) :
    ⦃⌜n = 2 * (k - 1) ∧ isHermitianSymmetric a ∧ k > 0⌝⦄
    irfft a n
    ⦃⇓result => ⌜
      -- Length preservation: output length matches specified n
      (result.toList.length = n) ∧
      -- DC component preservation: first element is real when input DC is real
      ((a.get ⟨0, h_nonempty⟩).im = 0 → 
        ∃ i : Fin n, result.get i = (a.get ⟨0, h_nonempty⟩).re) ∧
      -- Symmetry property: result has the symmetry properties of real-valued inverse FFT
      (∀ i : Fin n, ∀ j : Fin n, (i.val + j.val = n) → 
        result.get i = result.get j) ∧
      -- Hermitian input constraint: the input must be Hermitian-symmetric
      (isHermitianSymmetric a) ∧
      -- Length relationship: output length is twice the input length minus 2
      (n = 2 * (k - 1))
    ⌝⦄ := by
  apply do.pure
  constructor
  · exact Vector.toList_length
  constructor
  · intro h_im_zero
    use ⟨0, by omega⟩
    rfl
  constructor
  · intro i j h_sum
    rfl
  constructor
  · exact h_hermitian
  · exact h_length