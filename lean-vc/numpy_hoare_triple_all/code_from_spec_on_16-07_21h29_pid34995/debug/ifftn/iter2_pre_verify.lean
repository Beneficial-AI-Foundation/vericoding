import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.fft.ifftn",
  "description": "Compute the N-dimensional inverse discrete Fourier Transform",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.fft.ifftn.html",
  "doc": "numpy.fft.ifftn(a, s=None, axes=None, norm=None, out=None)\n\nCompute the N-dimensional inverse discrete Fourier Transform using the Fast Fourier Transform (FFT). It is the inverse of the N-dimensional FFT, such that ifftn(fftn(a)) == a within numerical accuracy.\n\nParameters:\n- a: Input array (can be complex)\n- s: Optional sequence of integers specifying output shape\n- axes: Optional sequence of axes to transform\n- norm: Optional normalization mode (\"backward\", \"ortho\", \"forward\")\n- out: Optional output array\n\nReturns:\n- Complex ndarray transformed along specified axes, potentially truncated or zero-padded\n\nExample:\nimport numpy as np\na = np.eye(4)\nnp.fft.ifftn(np.fft.fftn(a, axes=(0,)), axes=(1,))",
  "code": "@array_function_dispatch(_fftn_dispatcher)\ndef ifftn(a, s=None, axes=None, norm=None, out=None):\n    \"\"\"\n    Compute the N-dimensional inverse discrete Fourier Transform.\n    \"\"\"\n    return _raw_fftnd(a, s, axes, ifft, norm, out=out)"
}
-/

open Std.Do

set_option linter.missingDocs false

/-- Complex number type for IFFTN operations -/
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

-- LLM HELPER
def computeIFFTNElement {m n : Nat} (a : Vector (ComplexVector n) m) (i : Fin m) (j : Fin n) : Complex :=
  (1.0 / (m.toFloat * n.toFloat)) * 
  complexSum (fun k => complexSum (fun l =>
    (a.get k).get l * cexp (2 * (3.14159265358979323846 : Float) * 
      (i.val.toFloat * k.val.toFloat / m.toFloat + j.val.toFloat * l.val.toFloat / n.toFloat))))

-- LLM HELPER
def buildResultVector {m n : Nat} (a : Vector (ComplexVector n) m) : Vector (ComplexVector n) m :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => computeIFFTNElement a i j))

/-- Compute the N-dimensional inverse discrete Fourier Transform (IFFTN).
     
     The IFFTN extends the 1D inverse FFT to multiple dimensions, computing
     the inverse of the N-dimensional DFT. For a 2D array, this applies the
     inverse transform along both dimensions.
     
     For a 2D array of size m×n, the (i,j)-th output element is computed as:
     X[i,j] = (1/(m*n)) * Σ(k=0 to m-1) Σ(l=0 to n-1) a[k,l] * exp(2πi*(i*k/m + j*l/n))
     
     This is the mathematical inverse of the N-dimensional FFT. -/
def ifftn {m n : Nat} (a : Vector (ComplexVector n) m) : Id (Vector (ComplexVector n) m) :=
  buildResultVector a

-- LLM HELPER
lemma vector_get_ofFn {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  rfl

/-- Specification: The N-dimensional inverse FFT correctly computes the inverse discrete Fourier transform.
     
     The IFFTN satisfies the inverse N-dimensional DFT equation where each output element (i,j)
     is computed as (1/(m*n)) times the double sum over all input elements (k,l), multiplied by
     the complex exponential exp(2πi*(i*k/m + j*l/n)).
     
     This is the mathematical inverse of the N-dimensional FFT operation, with positive signs
     in the exponential and a normalization factor of 1/(m*n) for 2D case.
     
     Key properties:
     1. Inverse relationship: ifftn(fftn(x)) ≈ x within numerical accuracy
     2. Linearity: ifftn(a*x + b*y) = a*ifftn(x) + b*ifftn(y) 
     3. Parseval's theorem: energy is preserved with proper normalization
     4. Separability: N-D transform can be computed as sequence of 1-D transforms -/
theorem ifftn_spec {m n : Nat} (a : Vector (ComplexVector n) m) (hm : m > 0) (hn : n > 0) :
    ⦃⌜m > 0 ∧ n > 0⌝⦄
    ifftn a
    ⦃⇓result => ⌜∀ i : Fin m, ∀ j : Fin n,
        (result.get i).get j = (1.0 / (m.toFloat * n.toFloat)) * 
        complexSum (fun k => complexSum (fun l =>
            (a.get k).get l * cexp (2 * (3.14159265358979323846 : Float) * 
                (i.val.toFloat * k.val.toFloat / m.toFloat + j.val.toFloat * l.val.toFloat / n.toFloat))))⌝⦄ := by
  exact fun h i j => by simp [ifftn, buildResultVector, vector_get_ofFn, computeIFFTNElement]