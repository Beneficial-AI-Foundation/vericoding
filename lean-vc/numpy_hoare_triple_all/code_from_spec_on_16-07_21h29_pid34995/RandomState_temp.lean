import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.random.RandomState",
  "description": "Container for the slow Mersenne Twister pseudo-random number generator",
  "url": "https://numpy.org/doc/stable/reference/random/legacy.html#numpy.random.RandomState",
  "doc": "RandomState(seed=None)\n\nContainer for the slow Mersenne Twister pseudo-random number generator.\n\nConsider using the more modern np.random.Generator instead.\n\nRandomState is effectively frozen and will only receive updates required for compatibility.\n\nParameters:\n- seed : None, int, array_like[ints], SeedSequence, BitGenerator, Generator\n    Random seed initializing the pseudo-random number generator",
  "code": "Legacy random number generator class"
}
-/

/-- A simple random state container that can generate random numbers
    This models the core functionality of numpy.random.RandomState.
    We focus on the random() method which generates random floats in [0, 1).
-/
structure RandomState where
  /-- The seed value used to initialize the random number generator -/
  seed : Nat

-- LLM HELPER
/-- Simple linear congruential generator to create a deterministic pseudo-random value -/
def lcg (seed : Nat) : Nat :=
  (seed * 1103515245 + 12345) % (2^31)

-- LLM HELPER
/-- Convert a natural number to a float in [0, 1) -/
def natToUnitFloat (n : Nat) : Float :=
  (n.toFloat) / (2^31).toFloat

/-- Generate a random float in the range [0, 1) using the RandomState
    This models the RandomState.random() method which is the most fundamental
    operation for generating uniformly distributed random numbers.
-/
def random (state : RandomState) : Id Float :=
  natToUnitFloat (lcg state.seed)

-- LLM HELPER
/-- Lemma: lcg produces values less than 2^31 -/
lemma lcg_bound (seed : Nat) : lcg seed < 2^31 := by
  simp [lcg]
  exact Nat.mod_lt _ (by norm_num : (0 : Nat) < 2^31)

-- LLM HELPER
/-- Lemma: natToUnitFloat produces values in [0, 1) -/
lemma natToUnitFloat_range (n : Nat) (h : n < 2^31) : 
  0 ≤ natToUnitFloat n ∧ natToUnitFloat n < 1 := by
  constructor
  · simp [natToUnitFloat]
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · norm_num
  · simp [natToUnitFloat]
    rw [div_lt_iff]
    · simp only [one_mul]
      exact Nat.cast_lt.mpr h
    · norm_num

/-- Specification: random generates a float in the range [0, 1)
    
    The random function should satisfy:
    1. The result is always in the range [0, 1)
    2. The result is deterministic given the same seed
    3. The result follows uniform distribution properties
-/
theorem random_spec (state : RandomState) :
    ⦃⌜True⌝⦄
    random state
    ⦃⇓result => ⌜0 ≤ result ∧ result < 1⌝⦄ := by
  simp [random]
  apply natToUnitFloat_range
  exact lcg_bound state.seed