import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Complex number type for FFT -/
structure Complex where
  /-- Real part of complex number -/
  re : Float
  /-- Imaginary part of complex number -/
  im : Float
deriving Repr

/-- Complex exponential function -/
def cexp (θ : Float) : Complex :=
  { re := Float.cos θ, im := Float.sin θ }

/-- Complex multiplication -/
instance : Mul Complex where
  mul z w := { re := z.re * w.re - z.im * w.im, im := z.re * w.im + z.im * w.re }

/-- Complex addition -/
instance : Add Complex where
  add z w := { re := z.re + w.re, im := z.im + w.im }

/-- Zero complex number -/
instance : Zero Complex where
  zero := { re := 0, im := 0 }

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

-- LLM HELPER
def computeDFT {n : Nat} (a : Vector Complex n) (k : Fin n) : Complex :=
  complexSum (fun j => a.get j * cexp (-2 * (3.14159265358979323846 : Float) * (k.val.toFloat * j.val.toFloat) / n.toFloat))

-- LLM HELPER
def vectorFromFunc {n : Nat} (f : Fin n → Complex) : Vector Complex n :=
  Vector.mk (Array.mk (List.map f (List.finRange n))) (by simp [List.length_map, List.length_finRange])

/-- Compute the one-dimensional discrete Fourier Transform

    The FFT computes the DFT defined as:
    X[k] = Σ(n=0 to N-1) x[n] * exp(-2πi*k*n/N)

    where:
    - x is the input vector
    - X is the output vector
    - N is the length of the vector
    - i is the imaginary unit
-/
def fft {n : Nat} (a : Vector Complex n) : Id (Vector Complex n) :=
  vectorFromFunc (fun k => computeDFT a k)

-- LLM HELPER
lemma vectorFromFunc_get {n : Nat} (f : Fin n → Complex) (i : Fin n) : 
    (vectorFromFunc f).get i = f i := by
  simp [vectorFromFunc, Vector.get, Array.get]
  have h : i.val < (List.map f (List.finRange n)).length := by
    simp [List.length_map, List.length_finRange]
    exact i.isLt
  rw [List.get_map f (List.finRange n) i.val h]
  rw [List.get_finRange]

-- LLM HELPER
lemma vectorFromFunc_size {n : Nat} (f : Fin n → Complex) : 
    (vectorFromFunc f).size = n := by
  simp [vectorFromFunc, Vector.size, Array.size]

-- LLM HELPER
lemma computeDFT_zero {n : Nat} (a : Vector Complex n) (h : n > 0) : 
    computeDFT a ⟨0, h⟩ = complexSum (fun j => a.get j) := by
  simp [computeDFT]
  congr
  ext j
  simp [cexp]
  have : (0 : Float) * j.val.toFloat = 0 := by ring
  simp [this]
  have : Float.cos 0 = 1 := by norm_num
  have : Float.sin 0 = 0 := by norm_num
  simp [this, Complex.mul]
  ring

/-- Specification: FFT computes the discrete Fourier transform

    The FFT satisfies the DFT equation and has the following properties:
    1. Each output element is the sum of input elements weighted by complex exponentials
    2. The transform is linear
    3. Parseval's theorem: energy is preserved (with proper normalization)
    4. FFT(FFT^(-1)(x)) = x (inverse property when combined with IFFT)

    The specification captures the fundamental DFT formula where each output
    element k is computed as the sum over all input elements j, multiplied
    by the complex exponential exp(-2πi*k*j/n).
-/
theorem fft_spec {n : Nat} (a : Vector Complex n) (h : n > 0) :
    ⦃⌜n > 0⌝⦄
    fft a
    ⦃⇓result => ⌜∀ k : Fin n,
        result.get k = complexSum (fun j =>
            a.get j * cexp (-2 * (3.14159265358979323846 : Float) * (k.val.toFloat * j.val.toFloat) / n.toFloat)) ∧
        -- Sanity check: output vector has same length as input
        result.size = n ∧
        -- FFT preserves the DC component (k=0) correctly
        (n > 0 → result.get ⟨0, h⟩ = complexSum (fun j => a.get j)) ∧
        -- FFT satisfies the fundamental DFT property for each frequency component
        (∀ k : Fin n, ∃ (sum : Complex), 
            sum = complexSum (fun j => a.get j * cexp (-2 * (3.14159265358979323846 : Float) * (k.val.toFloat * j.val.toFloat) / n.toFloat)) ∧
            result.get k = sum)⌝⦄ := by
  intro h_pre
  simp [fft]
  constructor
  · intro k
    simp [vectorFromFunc_get, computeDFT]
  constructor
  · simp [vectorFromFunc_size]
  constructor
  · intro h_pos
    simp [vectorFromFunc_get, computeDFT_zero]
  · intro k
    use computeDFT a k
    constructor
    · simp [computeDFT]
    · simp [vectorFromFunc_get]