import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.random.BitGenerator",
  "description": "Base class for bit generators",
  "url": "https://numpy.org/doc/stable/reference/random/bit_generators/index.html",
  "doc": "BitGenerator(seed=None)\n\nBase class for bit generators.\n\nThe BitGenerator has a limited set of responsibilities. It manages state and provides functions to produce random doubles and random unsigned 32- and 64-bit values.\n\nThis class should not be instantiated directly.",
  "code": "Abstract base class for bit generators"
}
-/

/-- BitGenerator state representing the internal state of a pseudo-random number generator.
    This is an abstract representation that can be seeded and used to generate random values.
-/
structure BitGeneratorState where
  /-- The seed value used to initialize the generator, or None if no seed was provided -/
  seed : Option UInt64
  /-- The internal state of the generator used for random number generation -/
  internal_state : UInt64

-- LLM HELPER
/-- Simple hash function to derive internal state from seed -/
def hash_seed (seed : UInt64) : UInt64 :=
  if seed = 0 then 1 else seed

/-- numpy.random.BitGenerator: Base class for bit generators.
    
    The BitGenerator manages state and provides functions to produce random doubles 
    and random unsigned 32- and 64-bit values. This function initializes a BitGenerator
    with an optional seed value.
    
    Parameters:
    - seed: Optional seed value to initialize the generator (None uses system entropy)
    
    Returns:
    - A BitGeneratorState that can be used to generate random values
-/
def numpy_random_BitGenerator (seed : Option UInt64) : Id BitGeneratorState :=
  match seed with
  | none => { seed := none, internal_state := 0 }
  | some s => { seed := some s, internal_state := hash_seed s }

-- LLM HELPER
lemma hash_seed_nonzero (seed : UInt64) : hash_seed seed ≠ 0 := by
  unfold hash_seed
  split_ifs with h
  · norm_num
  · exact h

/-- Specification: numpy.random.BitGenerator creates a properly initialized BitGenerator state.
    
    Precondition: True (any seed value is valid, including None)
    Postcondition: The returned state has the provided seed (or maintains None if no seed given)
                  and has a valid internal state representation.
-/
theorem numpy_random_BitGenerator_spec (seed : Option UInt64) :
    ⦃⌜True⌝⦄
    numpy_random_BitGenerator seed
    ⦃⇓result => ⌜result.seed = seed ∧ 
                 (seed.isSome → result.internal_state ≠ 0) ∧
                 (seed.isNone → result.internal_state = 0)⌝⦄ := by
  unfold numpy_random_BitGenerator
  cases seed with
  | none => 
    simp only [Option.isNone_none, Option.isSome_none, true_implies, and_true]
    rfl
  | some s => 
    simp only [Option.isSome_some, Option.isNone_some, false_implies, and_true, true_implies]
    constructor
    · rfl
    · exact hash_seed_nonzero s