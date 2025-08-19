import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.random.default_rng",
  "description": "Construct a new Generator with the default BitGenerator (PCG64)",
  "url": "https://numpy.org/doc/stable/reference/random/generator.html",
  "doc": "default_rng(seed=None)\n\nConstruct a new Generator with the default BitGenerator (PCG64).\n\nParameters:\n- seed : None, int, array_like[ints], SeedSequence, BitGenerator, Generator\n    A seed to initialize the BitGenerator. If None, fresh, unpredictable entropy will be pulled from the OS.\n\nReturns:\n- Generator\n    The initialized generator object",
  "code": "Factory function for creating Generator instances"
}
-/

/-- BitGenerator represents the underlying random number generator engine -/
structure BitGenerator where
  /-- Internal state of the generator -/
  state : Nat
  /-- Seed used to initialize the generator -/
  seed : Option Nat

/-- Generator provides high-level random number generation methods -/
structure Generator where
  /-- The underlying BitGenerator (PCG64 by default) -/
  bitGenerator : BitGenerator
  /-- Whether the generator has been properly initialized -/
  initialized : Bool

-- LLM HELPER
/-- Initialize the state based on the seed -/
def initializeState (seed : Option Nat) : Nat :=
  match seed with
  | none => 12345  -- Default entropy value when no seed provided
  | some s => if s = 0 then 1 else s + 1  -- Ensure non-zero state when seed is provided

/-- numpy.random.default_rng: Construct a new Generator with the default BitGenerator (PCG64).

    Creates a new Generator instance using PCG64 as the underlying BitGenerator.
    This is the recommended way to create random number generators in NumPy.
    
    If seed is None, the generator will be initialized with fresh entropy from the OS.
    If seed is provided, the generator will be deterministically initialized with that seed.
-/
def default_rng (seed : Option Nat := none) : Id Generator :=
  let bitGen : BitGenerator := {
    state := initializeState seed,
    seed := seed
  }
  let generator : Generator := {
    bitGenerator := bitGen,
    initialized := true
  }
  generator

/-- Specification: default_rng returns a properly initialized Generator object.

    Precondition: True (no restrictions on the seed parameter)
    Postcondition: The returned Generator is properly initialized with the given seed
    and uses PCG64 as the underlying BitGenerator.
-/
theorem default_rng_spec (seed : Option Nat := none) :
    ⦃⌜True⌝⦄
    default_rng seed
    ⦃⇓result => ⌜result.initialized = true ∧ 
                 result.bitGenerator.seed = seed ∧
                 (seed.isSome → result.bitGenerator.state ≠ 0)⌝⦄ := by
  simp [default_rng, initializeState]
  split
  · simp
  · simp
    split
    · simp
    · simp