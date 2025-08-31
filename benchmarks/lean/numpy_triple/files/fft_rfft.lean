/- 
{
  "name": "numpy.fft.rfft",
  "description": "Compute the one-dimensional discrete Fourier Transform for real input",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.fft.rfft.html",
  "doc": "numpy.fft.rfft(a, n=None, axis=-1, norm=None, out=None)\n\nCompute the one-dimensional discrete Fourier Transform for real input using an efficient Fast Fourier Transform (FFT) algorithm.\n\nParameters:\n- a: Input array\n- n: Optional number of points along transformation axis (default: input length)\n- axis: Axis to compute FFT (default: last axis)\n- norm: Normalization mode (\"backward\", \"ortho\", \"forward\")\n- out: Optional output array\n\nReturns:\n- A complex ndarray representing the transformed input. The length of the transformed axis is (n/2)+1 for even n, or (n+1)/2 for odd n.\n\nNotes:\n- Computes only non-negative frequency terms for real input\n- Exploits Hermitian symmetry of real input's Fourier transform\n- Silently discards any imaginary part of input\n\nExample:\nimport numpy as np\nnp.fft.rfft([0, 1, 0, 0])\n# Returns: array([ 1.+0.j,  0.-1.j, -1.+0.j])",
}
-/

/-  Compute the one-dimensional discrete Fourier Transform for real input.
    Returns only the non-negative frequency terms, exploiting Hermitian symmetry.
    The output length is (n/2)+1 for even n, or (n+1)/2 for odd n. -/

/-  Specification for rfft: 
    The real FFT computes the DFT of real-valued input, returning only non-negative frequency components.
    
    Mathematical properties:
    1. Output contains (n/2)+1 complex values representing frequencies 0 to n/2
    2. DC component (k=0) is always real (imaginary part is 0)
    3. For even n, Nyquist frequency (k=n/2) is also real
    4. The result represents the Discrete Fourier Transform for k = 0, 1, ..., n/2
    5. Each output[k] = Σ(j=0 to n-1) input[j] * exp(-2πi*k*j/n)
    
    Sanity checks:
    - For constant input signals, only the DC component is non-zero
    - The transform is linear: rfft(a + b) = rfft(a) + rfft(b)
    - Energy is preserved according to Parseval's theorem -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Complex number type for FFT results -/
structure Complex where
  /-- Real part -/
  re : Float
  /-- Imaginary part -/
  im : Float

/-- Complex exponential function -/
def cexp (θ : Float) : Complex :=
  { re := Float.cos θ, im := Float.sin θ }
/-- Complex multiplication -/
instance : Mul Complex where
  mul z w := { re := z.re * w.re - z.im * w.im, im := z.re * w.im + z.im * w.re }

/-- Zero complex number -/
instance : Zero Complex where
  zero := { re := 0, im := 0 }

/-- Complex addition -/
instance : Add Complex where
  add z w := { re := z.re + w.re, im := z.im + w.im }

/-- Convert Float to Complex -/
def Float.toComplex (x : Float) : Complex := { re := x, im := 0 }
/-- Sum of complex numbers over finite indices -/
def complexSum {n : Nat} (f : Fin n → Complex) : Complex :=
  match n with
  | 0 => 0
  | n + 1 =>
    let rec go : Fin (n + 1) → Complex
      | ⟨0, _⟩ => f ⟨0, by omega⟩
      | ⟨i + 1, h⟩ => f ⟨i + 1, h⟩ + go ⟨i, by omega⟩
    go ⟨n, by omega⟩

-- <vc-helpers>
-- </vc-helpers>

def rfft {n : Nat} (a : Vector Float n) : Id (Vector Complex ((n / 2) + 1)) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem rfft_spec {n : Nat} (a : Vector Float n) (h : n > 0) :
    ⦃⌜n > 0⌝⦄
    rfft a
    ⦃⇓result => ⌜∀ k : Fin ((n / 2) + 1), 
      result.get k = complexSum (fun j : Fin n =>
        (a.get j).toComplex * cexp (-2 * (3.14159265358979323846 : Float) * (k.val.toFloat * j.val.toFloat) / n.toFloat)) ∧
      -- DC component is real
      (if h0 : 0 < (n / 2) + 1 then (result.get ⟨0, h0⟩).im = 0 else True) ∧
      -- For even n, Nyquist frequency is real
      (n % 2 = 0 → (if hn : n / 2 < (n / 2) + 1 then (result.get ⟨n / 2, hn⟩).im = 0 else True))⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
