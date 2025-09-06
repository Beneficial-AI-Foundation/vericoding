/- 
{
  "name": "numpy.fft.ifft",
  "description": "Compute the one-dimensional inverse discrete Fourier Transform",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.fft.ifft.html",
  "doc": "numpy.fft.ifft(a, n=None, axis=-1, norm=None, out=None)\n\nCompute the one-dimensional inverse discrete Fourier Transform. It calculates the inverse of the one-dimensional n-point discrete Fourier transform, such that ifft(fft(a)) == a within numerical accuracy.\n\nParameters:\n- a: Input array (can be complex)\n- n: Optional length of transformed axis (default: input length)\n- axis: Axis to compute inverse DFT (default: last axis)\n- norm: Normalization mode (\"backward\", \"ortho\", \"forward\")\n- out: Optional output array\n\nReturns:\n- Complex ndarray: Transformed input, truncated or zero-padded\n\nNotes:\n- Input should be ordered like FFT output\n- Padding zeros at the end is common but can produce surprising results\n- Zero frequency term is at a[0]\n\nExample:\nimport numpy as np\nnp.fft.ifft([0, 4, 0, 0])\n# Returns: array([ 1.+0.j,  0.+1.j, -1.+0.j,  0.-1.j])",
}
-/

/-  Compute the one-dimensional inverse discrete Fourier Transform (IFFT).

    The IFFT transforms frequency domain data back to the time domain,
    computing the inverse of the DFT such that ifft(fft(x)) ≈ x.

    For a vector of length n, the k-th coefficient is computed as:
    X[k] = (1/n) * Σ(j=0 to n-1) a[j] * exp(2πi*j*k/n) -/

/-  Specification: The inverse FFT correctly computes the inverse discrete Fourier transform.

    The IFFT satisfies the inverse DFT equation where each output element k is 
    computed as (1/n) times the sum over all input elements j, multiplied by the 
    complex exponential exp(2πi*k*j/n).

    This is the mathematical inverse of the FFT operation, with a positive sign 
    in the exponential and a normalization factor of 1/n. -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
set_option linter.missingDocs false

/-- Complex number type for IFFT operations -/
structure Complex where
  re : Float
  im : Float
  deriving Repr

/-- Complex addition -/
instance : Add Complex where
  add z w := { re := z.re + w.re, im := z.im + w.im }

/-- Complex multiplication -/
instance : Mul Complex where
  mul z w := { re := z.re * w.re - z.im * w.im, im := z.re * w.im + z.im * w.re }

/-- Complex scalar multiplication -/
instance : HMul Float Complex Complex where
  hMul s z := { re := s * z.re, im := s * z.im }

/-- Zero complex number -/
instance : Zero Complex where
  zero := { re := 0, im := 0 }

/-- Complex exponential function e^(iθ) -/
def cexp (θ : Float) : Complex :=
  { re := Float.cos θ, im := Float.sin θ }
/-- Sum of complex numbers over finite indices -/
def complexSum {n : Nat} (f : Fin n → Complex) : Complex :=
  match n with
  | 0 => 0
  | n + 1 =>
    let rec go : Fin (n + 1) → Complex
      | ⟨0, _⟩ => f ⟨0, by omega⟩
      | ⟨i + 1, h⟩ => f ⟨i + 1, h⟩ + go ⟨i, by omega⟩
    go ⟨n, by omega⟩
/-- Complex number vector type -/
abbrev ComplexVector (n : Nat) := Vector Complex n

-- <vc-helpers>
-- </vc-helpers>

def ifft {n : Nat} (a : ComplexVector n) : Id (ComplexVector n) :=
  sorry

theorem ifft_spec {n : Nat} (a : ComplexVector n) (h : n > 0) :
    ⦃⌜n > 0⌝⦄
    ifft a
    ⦃⇓result => ⌜∀ k : Fin n,
        result.get k = (1.0 / n.toFloat) * complexSum (fun j =>
            a.get j * cexp (2 * (3.14159265358979323846 : Float) * (k.val.toFloat * j.val.toFloat) / n.toFloat))⌝⦄ := by
  sorry
