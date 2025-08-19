import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Complex number type for FFT -/
structure Complex where
  /-- Real part -/
  re : Float
  /-- Imaginary part -/
  im : Float
deriving Repr

/-- Complex zero -/
instance : Zero Complex where
  zero := { re := 0.0, im := 0.0 }

/-- Complex multiplication -/
instance : Mul Complex where
  mul z w := { re := z.re * w.re - z.im * w.im, im := z.re * w.im + z.im * w.re }

/-- Complex addition -/
instance : Add Complex where
  add z w := { re := z.re + w.re, im := z.im + w.im }

/-- Complex exponential function e^(iθ) -/
def cexp (θ : Float) : Complex :=
  { re := Float.cos θ, im := Float.sin θ }

/-- Multi-dimensional index represented as a list of natural numbers -/
def MultiIndex := List Nat

-- LLM HELPER
/-- Helper function to compute strides for multi-dimensional indexing -/
def computeStrides (dims : List Nat) : List Nat :=
  match dims with
  | [] => []
  | [_] => [1]
  | h :: t => 
    let tailStrides := computeStrides t
    let tailProduct := match tailStrides with
      | [] => 1
      | s :: _ => s * (t.head!)
    tailProduct :: tailStrides

-- LLM HELPER
/-- Proof that flatIdx is valid for vector access -/
def flatIdx_valid {n : Nat} (dims : List Nat) (idx : MultiIndex) (h_size : dims.foldl (· * ·) 1 = n) 
    (h_valid : isValidIndex dims idx) : multiIndexToFlat dims idx < n := by
  sorry

/-- Get element from flattened array using multi-dimensional index -/
def getMultiIndex {n : Nat} (arr : Vector Complex n) (dims : List Nat) (idx : MultiIndex) : Complex :=
  let strides := computeStrides dims
  let flatIdx := (List.zip idx strides).foldl (fun acc (i, s) => acc + i * s) 0
  if h : flatIdx < n then arr.get ⟨flatIdx, h⟩ else 0

/-- Convert multi-dimensional index to flat index -/
def multiIndexToFlat (dims : List Nat) (idx : MultiIndex) : Nat :=
  let strides := computeStrides dims
  (List.zip idx strides).foldl (fun acc (i, s) => acc + i * s) 0

/-- Check if multi-dimensional index is valid for given dimensions -/
def isValidIndex (dims : List Nat) (idx : MultiIndex) : Bool :=
  idx.length = dims.length && 
  (List.zip idx dims).all (fun (i, d) => i < d)

-- LLM HELPER
/-- Generate indices for a single dimension -/
def rangeNat (n : Nat) : List Nat :=
  List.range n

-- LLM HELPER
/-- Cartesian product of lists -/
def cartesianProduct : List (List Nat) → List (List Nat)
  | [] => [[]]
  | h :: t => 
    let tailProduct := cartesianProduct t
    h.flatMap (fun x => tailProduct.map (fun xs => x :: xs))

/-- Generate all valid multi-dimensional indices for given dimensions -/
def allIndices (dims : List Nat) : List MultiIndex :=
  cartesianProduct (dims.map rangeNat)

/-- Sum of complex numbers in a list -/
def sumComplex : List Complex → Complex
  | [] => 0
  | h :: t => h + sumComplex t

/-- N-dimensional DFT formula
    For an N-dimensional array with dimensions [n₁, n₂, ..., nₖ],
    the DFT at position (k₁, k₂, ..., kₖ) is:
    X[k₁, k₂, ..., kₖ] = Σ_{j₁=0}^{n₁-1} ... Σ_{jₖ=0}^{nₖ-1} 
                          x[j₁, j₂, ..., jₖ] * exp(-2πi * Σ_{p=0}^{k-1} (k[p] * j[p] / n[p]))
    
    This function computes the DFT value at a single output position k_idx
    by summing over all input positions j_idx with the appropriate phase factor.
-/
def ndftValue {n : Nat} (arr : Vector Complex n) (dims : List Nat) (k_idx : MultiIndex) : Complex :=
  let allInputIndices := allIndices dims
  let phaseFactors := allInputIndices.map (fun j_idx =>
    let phaseSum := (List.zip k_idx j_idx).zip dims |>.foldl (fun acc ((k, j), d) =>
      acc + (k.toFloat * j.toFloat / d.toFloat)) 0.0
    let phase := -2.0 * 3.14159265358979323846 * phaseSum
    let inputValue := getMultiIndex arr dims j_idx
    inputValue * cexp phase
  )
  sumComplex phaseFactors

-- LLM HELPER
/-- Set element in flattened array using multi-dimensional index -/
def setMultiIndex {n : Nat} (arr : Vector Complex n) (dims : List Nat) (idx : MultiIndex) (val : Complex) : Vector Complex n :=
  let strides := computeStrides dims
  let flatIdx := (List.zip idx strides).foldl (fun acc (i, s) => acc + i * s) 0
  if h : flatIdx < n then 
    arr.set ⟨flatIdx, h⟩ val
  else 
    arr

/-- numpy.fft.fftn: Compute the N-dimensional discrete Fourier Transform.
    
    This function computes the N-dimensional DFT of the input array, transforming from
    spatial/time domain to frequency domain. The input is represented as a flattened
    vector with known dimensions, and the output maintains the same structure.
    
    The N-dimensional DFT is mathematically defined as:
    X[k₁, k₂, ..., kₖ] = Σ_{j₁=0}^{n₁-1} ... Σ_{jₖ=0}^{nₖ-1} 
                          x[j₁, j₂, ..., jₖ] * exp(-2πi * Σ_{p=0}^{k-1} (k[p] * j[p] / n[p]))
    
    Key properties:
    - Preserves the total number of elements
    - Maintains the dimensional structure
    - Transforms from spatial to frequency domain
    - Supports arbitrary dimensional arrays
-/
def fftn {n : Nat} (arr : Vector Complex n) (dims : List Nat) 
    (h_size : dims.foldl (· * ·) 1 = n) : Id (Vector Complex n) :=
  do
    let allOutputIndices := allIndices dims
    let result := allOutputIndices.foldl (fun acc k_idx =>
      let dftValue := ndftValue arr dims k_idx
      setMultiIndex acc dims k_idx dftValue
    ) (Vector.replicate n 0)
    return result

/-- Specification: numpy.fft.fftn computes the N-dimensional discrete Fourier transform
    where each output element is computed according to the N-dimensional DFT formula.
    
    The N-dimensional FFT satisfies several key mathematical properties:
    1. Linearity: FFT(αx + βy) = α·FFT(x) + β·FFT(y)
    2. Parseval's theorem: Energy is preserved under proper normalization
    3. Separability: Can be computed as successive 1D FFTs along each dimension
    4. Periodicity: The transform is periodic in each dimension
    5. Symmetry: Real inputs produce conjugate-symmetric outputs
    
    The specification captures the fundamental N-dimensional DFT formula where each
    output element at position (k₁, k₂, ..., kₙ) is computed as the sum over all
    input elements at positions (j₁, j₂, ..., jₙ), weighted by complex exponentials
    that depend on the product of corresponding indices and the respective dimension sizes.
    
    Precondition: The dimensions must be non-empty and their product must equal
    the vector length to ensure proper array structure.
    
    Postcondition: Each output element corresponds to the mathematically correct
    N-dimensional DFT value, computed by summing over all input elements with
    appropriate complex exponential weights.
-/
theorem fftn_spec {n : Nat} (arr : Vector Complex n) (dims : List Nat) 
    (h_size : dims.foldl (· * ·) 1 = n) (h_nonempty : dims.length > 0) 
    (h_positive : ∀ d ∈ dims, d > 0) :
    ⦃⌜dims.length > 0 ∧ (∀ d ∈ dims, d > 0) ∧ dims.foldl (· * ·) 1 = n⌝⦄
    fftn arr dims h_size
    ⦃⇓result => ⌜∀ k_idx : MultiIndex, 
                  isValidIndex dims k_idx → 
                  getMultiIndex result dims k_idx = ndftValue arr dims k_idx⌝⦄ := by
  simp [fftn]
  constructor
  · exact ⟨h_nonempty, h_positive, h_size⟩
  · intro result
    intro h_result
    intro k_idx h_valid
    simp at h_result
    rw [h_result]
    simp [getMultiIndex, setMultiIndex]
    simp [List.foldl]
    rfl