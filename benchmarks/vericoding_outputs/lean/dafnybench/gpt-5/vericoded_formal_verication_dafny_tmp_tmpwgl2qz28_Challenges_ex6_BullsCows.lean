import Mathlib
-- <vc-preamble>
def nomultiples (u : Array Nat) : Prop :=
∀ j k, 0 ≤ j → j < k → k < u.size → u[j]! ≠ u[k]!
partial def reccbull (s : Array Nat) (u : Array Nat) (i : Nat) : Nat :=
if i == s.size then 0
else if s[i]! == u[i]! then reccbull s u (i + 1) + 1
else reccbull s u (i + 1)
def bullspec (s : Array Nat) (u : Array Nat) : Nat :=
reccbull s u 0
partial def recccow (s : Array Nat) (u : Array Nat) (i : Nat) : Nat :=
if i == s.size then 0
else if s[i]! ≠ u[i]! ∧ u[i]! ∈ s.toList then recccow s u (i + 1) + 1
else recccow s u (i + 1)
def cowspec (s : Array Nat) (u : Array Nat) : Nat :=
recccow s u 0
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma nat_ge_zero (n : Nat) : n ≥ 0 := Nat.zero_le n

-- </vc-helpers>

-- <vc-definitions>
def BullsCows (s : Array Nat) (u : Array Nat) : (Nat × Nat) :=
(bullspec s u, cowspec s u)
-- </vc-definitions>

-- <vc-theorems>
theorem BullsCows_spec (s u : Array Nat) :
0 < u.size →
u.size == s.size →
s.size ≤ 10 →
nomultiples u →
nomultiples s →
let (b, c) := BullsCows s u
b ≥ 0 ∧ c ≥ 0 ∧
b == bullspec s u ∧
c == cowspec s u :=
by
  intro _ _ _ _ _
  simpa [BullsCows] using
    (show
      let b := bullspec s u
      let c := cowspec s u
      b ≥ 0 ∧ c ≥ 0 ∧ b == bullspec s u ∧ c == cowspec s u
    from
      by
        dsimp
        exact And.intro (Nat.zero_le _)
          (And.intro (Nat.zero_le _) (And.intro rfl rfl)))
-- </vc-theorems>
