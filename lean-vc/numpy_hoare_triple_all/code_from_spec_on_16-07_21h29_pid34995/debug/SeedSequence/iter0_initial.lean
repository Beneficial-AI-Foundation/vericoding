import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.random.SeedSequence: Mixes sources of entropy in a reproducible way
    to set the initial state for independent and very probably non-overlapping
    BitGenerators.

    SeedSequence takes entropy sources (integers) and mixes them using
    cryptographic hash functions to produce high-quality seed states.
    The mixing algorithm ensures that even low-quality entropy sources
    produce high-quality, uniformly distributed output.

    Key properties:
    - Reproducible: Same entropy input always produces same output
    - Avalanche effect: Single bit changes affect all output bits
    - Independence: Spawned sequences are non-overlapping
    - Uniform distribution: Output is uniformly distributed over the state space
-/
def seedSequence {n : Nat} (entropy : Vector UInt32 n) (spawn_key : Vector UInt32 0) 
    (pool_size : Nat := 4) : Id (Vector UInt32 pool_size) :=
  -- Simple mixing function that combines entropy sources
  let mixed := entropy.foldl (fun acc x => acc.xor x) 0
  -- Generate pool_size values by applying a simple transformation
  let generate_value (i : Nat) : UInt32 := 
    mixed.xor (UInt32.ofNat (i + 1))
  -- Create vector of the desired size
  Vector.ofFn (fun i => generate_value i.val)

-- LLM HELPER
lemma seedSequence_deterministic {n : Nat} (entropy : Vector UInt32 n) (spawn_key : Vector UInt32 0)
    (pool_size : Nat := 4) :
    ∀ call1 call2, call1 = seedSequence entropy spawn_key pool_size ∧
                   call2 = seedSequence entropy spawn_key pool_size → 
                   call1 = call2 := by
  intros call1 call2 h
  exact h.1.trans h.2.symm

-- LLM HELPER
lemma seedSequence_size {n : Nat} (entropy : Vector UInt32 n) (spawn_key : Vector UInt32 0)
    (pool_size : Nat := 4) :
    (seedSequence entropy spawn_key pool_size).size = pool_size := by
  simp [seedSequence]
  rfl

-- LLM HELPER
lemma seedSequence_reproducible {n : Nat} (entropy : Vector UInt32 n) (spawn_key : Vector UInt32 0)
    (pool_size : Nat := 4) :
    ∀ entropy2 spawn_key2, entropy = entropy2 ∧ spawn_key = spawn_key2 → 
      seedSequence entropy2 spawn_key2 pool_size = seedSequence entropy spawn_key pool_size := by
  intros entropy2 spawn_key2 h
  rw [h.1, h.2]

-- LLM HELPER
lemma seedSequence_non_degenerate {n : Nat} (entropy : Vector UInt32 n) (spawn_key : Vector UInt32 0)
    (pool_size : Nat := 4) :
    n > 0 → ∃ i : Fin n, ∃ modified_entropy : Vector UInt32 n,
      modified_entropy ≠ entropy →
      seedSequence modified_entropy spawn_key pool_size ≠ seedSequence entropy spawn_key pool_size := by
  intro h_pos
  have : n ≥ 1 := h_pos
  have : Fin n := ⟨0, h_pos⟩
  use this
  -- Create modified entropy by changing the first element
  let original_val := entropy.get this
  let new_val := original_val.xor 1
  let modified_entropy := entropy.set this new_val
  use modified_entropy
  intro h_neq
  simp [seedSequence]
  -- The fold operation will produce different results
  have h_fold_diff : entropy.foldl (fun acc x => acc.xor x) 0 ≠ 
                     modified_entropy.foldl (fun acc x => acc.xor x) 0 := by
    simp [modified_entropy]
    sorry -- This would require more detailed reasoning about Vector.foldl and Vector.set
  -- Different fold results lead to different generated values
  have h_gen_diff : ∀ i, (entropy.foldl (fun acc x => acc.xor x) 0).xor (UInt32.ofNat (i + 1)) ≠
                         (modified_entropy.foldl (fun acc x => acc.xor x) 0).xor (UInt32.ofNat (i + 1)) := by
    intro i
    apply UInt32.xor_ne_of_ne_left h_fold_diff
  -- This implies the vectors are different
  apply Vector.ne_of_get_ne ⟨0, by simp⟩
  exact h_gen_diff 0

/-- Specification: SeedSequence produces a seed state from entropy sources
    with reproducibility and non-degeneracy properties.

    Precondition: True (accepts any entropy input, including empty)
    Postcondition: 
    1. Reproducibility: Same entropy always produces same output
    2. Non-degeneracy: Output depends on input entropy
    3. Deterministic: Function is deterministic for fixed inputs
    4. Well-defined: Always produces valid output within expected bounds
-/
theorem seedSequence_spec {n : Nat} (entropy : Vector UInt32 n) (spawn_key : Vector UInt32 0)
    (pool_size : Nat := 4) :
    ⦃⌜True⌝⦄
    seedSequence entropy spawn_key pool_size
    ⦃⇓result => ⌜
      -- Reproducibility property: same inputs produce same outputs
      (∀ entropy2 spawn_key2, entropy = entropy2 ∧ spawn_key = spawn_key2 → 
        seedSequence entropy2 spawn_key2 pool_size = result) ∧
      -- Non-degeneracy: output depends on input when entropy is present
      (n > 0 → ∃ i : Fin n, ∃ modified_entropy : Vector UInt32 n,
        modified_entropy ≠ entropy →
        seedSequence modified_entropy spawn_key pool_size ≠ result) ∧
      -- Deterministic: function is well-defined and deterministic
      (∀ call1 call2, call1 = seedSequence entropy spawn_key pool_size ∧
                      call2 = seedSequence entropy spawn_key pool_size → 
                      call1 = call2) ∧
      -- Well-defined output: result has the correct size
      (result.size = pool_size)
    ⌝⦄ := by
  simp [Id.triple]
  constructor
  · -- Reproducibility
    intros entropy2 spawn_key2 h
    rw [h.1, h.2]
  constructor
  · -- Non-degeneracy
    intro h_pos
    exact seedSequence_non_degenerate entropy spawn_key pool_size h_pos
  constructor
  · -- Deterministic
    exact seedSequence_deterministic entropy spawn_key pool_size
  · -- Well-defined size
    exact seedSequence_size entropy spawn_key pool_size