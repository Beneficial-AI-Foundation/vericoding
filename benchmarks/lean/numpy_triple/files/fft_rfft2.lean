/- 
{
  "name": "numpy.fft.rfft2",
  "description": "Compute the 2-dimensional FFT of a real array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.fft.rfft2.html",
  "doc": "numpy.fft.rfft2(a, s=None, axes=(-2, -1), norm=None, out=None)\n\nCompute the 2-dimensional FFT of a real array.\n\nParameters:\n- a: Input array, taken to be real\n- s: Optional shape of the FFT (sequence of ints)\n- axes: Axes over which to compute the FFT (default: (-2, -1))\n- norm: Normalization mode (\"backward\", \"ortho\", \"forward\")\n- out: Optional output array for the result\n\nReturns:\n- Complex ndarray representing the result of the real 2-D FFT\n\nNotes:\n- This is essentially rfftn with different default behavior\n- Introduced for computing Fourier transforms on real-valued 2D arrays\n\nExample:\nimport numpy as np\na = np.mgrid[:5, :5][0]\nnp.fft.rfft2(a)",
}
-/

/-  Compute the 2-dimensional FFT of a real array.

    This function transforms a real 2D array into the frequency domain using
    a 2D Fast Fourier Transform. The transformation is performed over the
    last two axes by default.

    The key difference from fft2 is that this function starts with real input
    and exploits the Hermitian symmetry property to compute only the 
    non-negative frequency components along the last axis, making it more
    efficient for real-valued input data.

    Output dimensions: For input of shape (m+1, n+1), output has shape (m+1, (n+1)/2+1)
    where the last dimension is reduced due to Hermitian symmetry. -/

/-  Specification for rfft2: 2D FFT of real input array

    Mathematical properties:
    1. Two-stage transformation: first axis uses complex FFT, second axis uses real FFT
    2. Output shape is (m+1, (n+1)/2+1) for input shape (m+1, n+1)
    3. Hermitian symmetry: Due to real input, negative frequencies are redundant
    4. DC component preservation: The (0,0) element is always real
    5. Energy conservation: Follows Parseval's theorem with proper normalization

    The transformation can be mathematically expressed as:
    result[k,l] = Σ_{p=0}^{m} Σ_{q=0}^{n} input[p,q] * exp(-2πi(kp/(m+1) + lq/(n+1)))
    for k ∈ [0, m] and l ∈ [0, (n+1)/2] (exploiting Hermitian symmetry)

    Sanity checks:
    - For zero input, output is all zeros
    - For constant input, only DC component (0,0) is non-zero
    - Transform preserves linearity: rfft2(a + b) = rfft2(a) + rfft2(b)
    - Last axis has reduced size due to real input optimization -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Complex number type for FFT results -/
structure Complex where
  /-- Real part -/
  re : Float
  /-- Imaginary part -/
  im : Float

/-- Complex zero -/
instance : Zero Complex where
  zero := { re := 0, im := 0 }

/-- Complex addition -/
instance : Add Complex where
  add z w := { re := z.re + w.re, im := z.im + w.im }

/-- Complex multiplication -/
instance : Mul Complex where
  mul z w := { re := z.re * w.re - z.im * w.im, im := z.re * w.im + z.im * w.re }

/-- Complex exponential function e^(iθ) -/
def cexp (θ : Float) : Complex :=
  { re := Float.cos θ, im := Float.sin θ }
/-- Convert Float to Complex -/
def Float.toComplex (x : Float) : Complex := { re := x, im := 0 }

-- <vc-helpers>
-- </vc-helpers>

def rfft2 {m n : Nat} (a : Vector (Vector Float (n + 1)) (m + 1)) : Id (Vector (Vector Complex (((n + 1) / 2) + 1)) (m + 1)) :=
  sorry

theorem rfft2_spec {m n : Nat} (a : Vector (Vector Float (n + 1)) (m + 1)) :
    ⦃⌜True⌝⦄
    rfft2 a
    ⦃⇓result => ⌜∀ k : Fin (m + 1), ∀ l : Fin (((n + 1) / 2) + 1),
      -- Each output element is computed via the 2D DFT formula
      (result.get k).get l = 
        (Vector.foldl (fun acc_p p => 
          Vector.foldl (fun acc_q q => 
            let phase := -2 * (3.14159265358979323846 : Float) * 
                        (k.val.toFloat * p.val.toFloat / (m + 1).toFloat + 
                         l.val.toFloat * q.val.toFloat / (n + 1).toFloat)
            let weight := cexp phase
            let term := ((a.get p).get q).toComplex * weight
            acc_q + term
          ) acc_p (Vector.ofFn (fun q : Fin (n + 1) => q))
        ) 0 (Vector.ofFn (fun p : Fin (m + 1) => p))) ∧
      -- DC component is real (imaginary part is zero)
      ((result.get ⟨0, by omega⟩).get ⟨0, by omega⟩).im = 0 ∧
      -- Last axis is reduced size due to Hermitian symmetry
      (result.get ⟨0, by omega⟩).size = ((n + 1) / 2) + 1⌝⦄ := by
  sorry
