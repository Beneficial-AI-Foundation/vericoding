-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def DNA_strand : List Base → List Base
  | xs => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dna_complement_length {xs : List Base} :
  (DNA_strand xs).length = xs.length := by sorry

theorem dna_complement_involution {xs : List Base} :
  DNA_strand (DNA_strand xs) = xs := by sorry

theorem dna_complement_maps_correctly {xs : List Base} {i : Nat} (h : i < xs.length) :
  match xs.get ⟨i, h⟩ with
  | Base.A => (DNA_strand xs).get ⟨i, by {rw [dna_complement_length]; exact h}⟩ = Base.T
  | Base.T => (DNA_strand xs).get ⟨i, by {rw [dna_complement_length]; exact h}⟩ = Base.A
  | Base.C => (DNA_strand xs).get ⟨i, by {rw [dna_complement_length]; exact h}⟩ = Base.G
  | Base.G => (DNA_strand xs).get ⟨i, by {rw [dna_complement_length]; exact h}⟩ = Base.C
  := by sorry

/-
info: 'TTTT'
-/
-- #guard_msgs in
-- #eval DNA_strand "AAAA"

/-
info: 'TAACG'
-/
-- #guard_msgs in
-- #eval DNA_strand "ATTGC"

/-
info: 'CATA'
-/
-- #guard_msgs in
-- #eval DNA_strand "GTAT"
-- </vc-theorems>