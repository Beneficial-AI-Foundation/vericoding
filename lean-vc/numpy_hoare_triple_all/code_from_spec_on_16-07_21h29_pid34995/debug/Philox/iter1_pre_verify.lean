import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def philox_hash (x : Nat) : Nat :=
  let x1 := x ^^^ (x >>> 16)
  let x2 := x1 * 0x85ebca6b
  let x3 := x2 ^^^ (x2 >>> 13)
  let x4 := x3 * 0xc2b2ae35
  x4 ^^^ (x4 >>> 16)

-- LLM HELPER
def nat_to_float_01 (n : Nat) : Float :=
  let normalized := n % 4294967296  -- 2^32
  Float.ofNat normalized / 4294967296.0

/-- Philox (4x64) pseudo-random number generator.
    
    Philox is a counter-based RNG that generates pseudo-random numbers
    using a counter and key. It provides high-quality random numbers
    with a large period (2^256 - 1) and supports parallel generation.
    
    The core operation takes a seed and generates a vector of random
    numbers in the range [0, 1).
-/
def philox {n : Nat} (seed : Nat) : Id (Vector Float n) :=
  let generate_at (i : Nat) : Float := nat_to_float_01 (philox_hash (seed + i))
  pure (Vector.ofFn generate_at)

-- LLM HELPER
lemma nat_to_float_01_range (n : Nat) : 0 ≤ nat_to_float_01 n ∧ nat_to_float_01 n < 1 := by
  simp [nat_to_float_01]
  constructor
  · -- 0 ≤ nat_to_float_01 n
    apply div_nonneg
    · apply Float.ofNat_nonneg
    · norm_num
  · -- nat_to_float_01 n < 1
    apply div_lt_one_of_lt
    · apply Float.ofNat_nonneg
    · apply Float.ofNat_lt_ofNat.mpr
      exact Nat.mod_lt _ (by norm_num : (0 : Nat) < 4294967296)
    · norm_num

-- LLM HELPER
lemma philox_deterministic {n : Nat} (seed₁ seed₂ : Nat) : 
    seed₁ = seed₂ → (philox seed₁ : Id (Vector Float n)) = (philox seed₂ : Id (Vector Float n)) := by
  intro h
  simp [philox, h]

/-- Specification: Philox generates pseudo-random numbers with deterministic behavior.
    
    The Philox algorithm has several key mathematical properties:
    1. Deterministic: same seed produces same sequence
    2. Uniform distribution: values are uniformly distributed in [0, 1)
    3. Range constraint: all values are in the half-open interval [0, 1)
    4. Reproducibility: identical seeds produce identical sequences
    
    Precondition: True (no special preconditions)
    Postcondition: All values are in [0, 1) and sequence is deterministic based on seed
-/
theorem philox_spec {n : Nat} (seed : Nat) :
    ⦃⌜True⌝⦄
    philox seed
    ⦃⇓result => ⌜(∀ i : Fin n, 0 ≤ result.get i ∧ result.get i < 1) ∧
                  (∀ seed₁ seed₂ : Nat, seed₁ = seed₂ → (philox seed₁ : Id (Vector Float n)) = (philox seed₂ : Id (Vector Float n)))⌝⦄ := by
  simp [HTri.pure]
  constructor
  · -- Range property
    intro i
    simp [philox, Vector.get_ofFn]
    exact nat_to_float_01_range _
  · -- Deterministic property
    exact philox_deterministic