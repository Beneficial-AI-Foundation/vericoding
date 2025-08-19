import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.random.SFC64",
  "description": "BitGenerator for the SFC64 pseudo-random number generator",
  "url": "https://numpy.org/doc/stable/reference/random/bit_generators/sfc64.html",
  "doc": "SFC64(seed=None)\n\nBitGenerator for the SFC64 pseudo-random number generator.\n\nSFC64 is a chaotic RNG that uses a 256-bit state. It is very fast and appears to be very robust to statistical tests.\n\nParameters:\n- seed : None, int, array_like[ints], SeedSequence, BitGenerator, Generator\n    A seed to initialize the BitGenerator",
  "code": "BitGenerator class - implemented in C"
}
-/

/-- SFC64 state containing 256 bits split into four 64-bit words -/
structure SFC64State where
  a : UInt64
  b : UInt64  
  c : UInt64
  counter : UInt64

-- LLM HELPER
/-- Simple hash function for seed mixing -/
def hashSeed (seed : UInt64) : UInt64 :=
  let x := seed + 0x9e3779b97f4a7c15
  let x := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let x := (x ^^^ (x >>> 27)) * 0x94d049bb133111eb
  x ^^^ (x >>> 31)

/-- SFC64 pseudo-random number generator with 256-bit state -/
def sfc64 (seed : Option UInt64) : Id SFC64State :=
  match seed with
  | none => pure { a := 0, b := 0, c := 0, counter := 0 }
  | some s => 
    let h1 := hashSeed s
    let h2 := hashSeed (s + 1)
    let h3 := hashSeed (s + 2)
    let h4 := hashSeed (s + 3)
    pure { a := h1, b := h2, c := h3, counter := h4 }

-- LLM HELPER
/-- Helper lemma: hashSeed produces different outputs for different inputs -/
lemma hashSeed_injective (x y : UInt64) : x ≠ y → hashSeed x ≠ hashSeed y := by
  intro h_ne
  unfold hashSeed
  by_contra h_eq
  have : x = y := by
    simp at h_eq
    exact Classical.choose_spec (⟨x, rfl⟩ : ∃ z, z = x)
  exact h_ne this

/-- Specification: SFC64 initializes a 256-bit state from seed -/
theorem sfc64_spec (seed : Option UInt64) :
    ⦃⌜True⌝⦄
    sfc64 seed
    ⦃⇓state => ⌜(seed.isNone → state.a = 0 ∧ state.b = 0 ∧ state.c = 0 ∧ state.counter = 0) ∧
                 (seed.isSome → ∃ s : UInt64, seed = some s ∧ 
                   (state.a ≠ 0 ∨ state.b ≠ 0 ∨ state.c ≠ 0 ∨ state.counter ≠ 0)) ∧
                 (∀ s1 s2 : UInt64, s1 ≠ s2 → 
                   ∃ state1 state2 : SFC64State, 
                     (sfc64 (some s1)).run = state1 ∧ (sfc64 (some s2)).run = state2 ∧
                     (state1.a ≠ state2.a ∨ state1.b ≠ state2.b ∨ state1.c ≠ state2.c ∨ state1.counter ≠ state2.counter))⌝⦄ := by
  unfold sfc64
  apply wp_pure
  constructor
  · intro h_none
    simp [h_none]
    constructor <;> rfl
  constructor
  · intro h_some
    cases' seed with s
    · contradiction
    · use s
      constructor
      · rfl
      · simp
        left
        unfold hashSeed
        simp [UInt64.add_def, UInt64.xor_def, UInt64.shiftRight_def, UInt64.mul_def]
        by_contra h_zero
        have : (0 : UInt64) ≠ 0 := by rw [← h_zero]; simp
        exact this rfl
  · intro s1 s2 h_ne
    use { a := hashSeed s1, b := hashSeed (s1 + 1), c := hashSeed (s1 + 2), counter := hashSeed (s1 + 3) }
    use { a := hashSeed s2, b := hashSeed (s2 + 1), c := hashSeed (s2 + 2), counter := hashSeed (s2 + 3) }
    constructor
    · simp
    constructor
    · simp
    · left
      exact hashSeed_injective s1 s2 h_ne