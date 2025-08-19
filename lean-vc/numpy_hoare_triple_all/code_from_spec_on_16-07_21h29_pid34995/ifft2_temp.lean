import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

set_option linter.missingDocs false

/-- Complex number type for IFFT2 operations -/
structure Complex where
  /-- Real part -/
  re : Float
  /-- Imaginary part -/
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

-- LLM HELPER
/-- Pi constant -/
def pi : Float := 3.14159265358979323846

/-- Complex exponential function e^(iθ) -/
def cexp (θ : Float) : Complex :=
  { re := Float.cos θ, im := Float.sin θ }

-- LLM HELPER
/-- Helper function to sum complex numbers over a finite range -/
def complexSum (f : Fin n → Complex) : Complex :=
  match n with
  | 0 => 0
  | n+1 => f ⟨0, Nat.zero_lt_succ n⟩ + complexSum (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

/-- Sum of complex numbers over 2D finite indices -/
def complexSum2D {m n : Nat} (f : Fin m → Fin n → Complex) : Complex :=
  complexSum (fun i => complexSum (fun j => f i j))

/-- 2D Inverse Discrete Fourier Transform formula for element (k, l) given input matrix of size m × n
    IDFT[k, l] = (1/(m*n)) * Σ_{p=0}^{m-1} Σ_{q=0}^{n-1} input[p, q] * e^(2πi(kp/m + lq/n))
-/
def idft2_element {m n : Nat} (input : Vector (Vector Complex n) m) (k : Fin m) (l : Fin n) : Complex :=
  let normFactor := 1.0 / (m.toFloat * n.toFloat)
  let sumValue := complexSum2D (fun p q => 
    let angle := 2.0 * pi * (k.val.toFloat * p.val.toFloat / m.toFloat + l.val.toFloat * q.val.toFloat / n.toFloat)
    (input.get p).get q * cexp angle)
  normFactor * sumValue

/-- numpy.fft.ifft2: Compute the 2-dimensional inverse discrete Fourier Transform.
    
    This function computes the 2D IDFT of the input matrix, transforming from
    frequency domain back to spatial/time domain. It is the inverse operation
    of the 2D FFT, such that ifft2(fft2(a)) ≈ a within numerical accuracy.
    
    The 2D IDFT uses positive exponentials and includes normalization by 1/(m*n).
-/
def numpy_ifft2 {m n : Nat} (a : Vector (Vector Complex n) m) : Id (Vector (Vector Complex n) m) :=
  Vector.ofFn (fun k => Vector.ofFn (fun l => idft2_element a k l))

/-- Specification: numpy.fft.ifft2 computes the 2D inverse discrete Fourier transform
    where each output element is computed using the inverse DFT formula.
    
    Precondition: Both dimensions must be positive for meaningful computation
    Postcondition: For all indices (k, l), the output element at position (k, l)
    equals the 2D IDFT formula applied to the input matrix.
    
    Mathematical properties:
    - Inverse relationship: ifft2(fft2(a)) ≈ a within numerical accuracy
    - Linearity: ifft2(α*a + β*b) = α*ifft2(a) + β*ifft2(b)
    - Energy preservation: Parseval's theorem with proper normalization
    - Conjugate symmetry preservation for real inputs
-/
theorem numpy_ifft2_spec {m n : Nat} (a : Vector (Vector Complex n) m) 
    (hm : m > 0) (hn : n > 0) :
    ⦃⌜m > 0 ∧ n > 0⌝⦄
    numpy_ifft2 a
    ⦃⇓result => ⌜∀ (k : Fin m) (l : Fin n), 
                  (result.get k).get l = idft2_element a k l⌝⦄ := by
  intro h
  simp [numpy_ifft2]
  intro k l
  simp [Vector.get_ofFn]