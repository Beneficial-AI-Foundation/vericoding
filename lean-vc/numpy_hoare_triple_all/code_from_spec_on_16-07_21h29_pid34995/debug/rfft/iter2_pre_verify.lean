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

-- LLM HELPER
def Nat.toFloat (n : Nat) : Float := Float.ofNat n

-- LLM HELPER
def Fin.toFloat (f : Fin n) : Float := Float.ofNat f.val

-- LLM HELPER
def Vector.ofFn {α : Type*} {n : Nat} (f : Fin n → α) : Vector α n :=
  Vector.mk (List.ofFn f) (by simp [List.length_ofFn])

/-- Compute the one-dimensional discrete Fourier Transform for real input.
    Returns only the non-negative frequency terms, exploiting Hermitian symmetry.
    The output length is (n/2)+1 for even n, or (n+1)/2 for odd n. -/
def rfft {n : Nat} (a : Vector Float n) : Id (Vector Complex ((n / 2) + 1)) :=
  let outputLength := (n / 2) + 1
  let computeCoeff (k : Fin outputLength) : Complex :=
    complexSum (fun j : Fin n =>
      (a.get j).toComplex * cexp (-2 * (3.14159265358979323846 : Float) * (k.val.toFloat * j.val.toFloat) / n.toFloat))
  Vector.ofFn computeCoeff

/-- Specification for rfft: 
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
  simp [HoareTriple.valid, rfft]
  constructor
  · intro k
    simp [Vector.get, Vector.ofFn]
    rfl
  constructor
  · intro h0
    simp [Vector.get, Vector.ofFn]
    simp [complexSum]
    simp [Float.toComplex, cexp]
    simp [Fin.toFloat]
    simp [Float.sin]
    rfl
  · intro heven hn
    simp [Vector.get, Vector.ofFn]
    simp [complexSum]
    simp [Float.toComplex, cexp]
    simp [Fin.toFloat]
    simp [Float.sin]
    rfl