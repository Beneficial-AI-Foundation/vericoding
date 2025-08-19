import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.random.PCG64",
  "description": "BitGenerator for the PCG-64 pseudo-random number generator",
  "url": "https://numpy.org/doc/stable/reference/random/bit_generators/pcg64.html",
  "doc": "PCG64(seed=None)\n\nBitGenerator for the PCG-64 pseudo-random number generator.\n\nPCG-64 is a 128-bit implementation of O'Neill's permutation congruential generator. It has a period of 2^128 and supports advancing an arbitrary number of steps as well as 2^127 streams.\n\nParameters:\n- seed : None, int, array_like[ints], SeedSequence, BitGenerator, Generator\n    A seed to initialize the BitGenerator",
  "code": "BitGenerator class - implemented in C"
}
-/

/-- PCG64 state representation: 128-bit internal state with 64-bit output -/
structure PCG64State where
  /-- Internal state of the PCG64 generator -/
  state : UInt64
  /-- Increment value (stream id) - must be odd for full period -/
  inc : UInt64

-- LLM HELPER
def default_pcg64_inc : UInt64 := 1442695040888963407

-- LLM HELPER
def hash_seed (s : UInt64) : UInt64 := s * 6364136223846793005 + 1

/-- PCG64 BitGenerator for pseudo-random number generation.
    
    PCG-64 is a 128-bit implementation of O'Neill's permutation congruential generator.
    It uses a linear congruential generator with output permutation (XOR shift left + random rotation).
    The generator has a period of 2^128 and supports advancing arbitrary steps.
-/
def pcg64 (seed : Option UInt64) : Id PCG64State :=
  match seed with
  | none => { state := 1, inc := default_pcg64_inc }
  | some s => { state := s, inc := default_pcg64_inc }

-- LLM HELPER
lemma default_inc_odd : default_pcg64_inc % 2 = 1 := by
  simp [default_pcg64_inc]
  norm_num

-- LLM HELPER
lemma uint64_nonneg (x : UInt64) : x ≥ 0 := by
  simp [UInt64.le_iff_toNat_le]

/-- Specification: PCG64 creates a valid pseudo-random number generator state.
    
    Precondition: The seed is either None or a valid 64-bit unsigned integer
    Postcondition: The generated state satisfies the PCG64 invariants:
    1. The state and increment values are properly initialized
    2. The increment value is odd (required for full period)
    3. The state is deterministic for a given seed
    4. Different seeds produce different initial states
-/
theorem pcg64_spec (seed : Option UInt64) :
    ⦃⌜True⌝⦄
    pcg64 seed
    ⦃⇓state => ⌜-- State invariants for PCG64
                 (state.inc % 2 = 1) ∧  -- Increment must be odd for full period
                 (state.state ≥ 0) ∧  -- State is non-negative
                 (state.inc ≥ 0) ∧  -- Increment is non-negative
                 (seed = none → state.state ≠ 0) ∧  -- Random seed produces non-zero state
                 (seed = some 0 → state.state = 0)⌝⦄ := by
  simp [pcg64, wp]
  cases seed with
  | none => 
    simp
    exact ⟨default_inc_odd, uint64_nonneg _, uint64_nonneg _, by simp, by simp⟩
  | some s =>
    simp
    exact ⟨default_inc_odd, uint64_nonneg _, uint64_nonneg _, by simp, by simp⟩