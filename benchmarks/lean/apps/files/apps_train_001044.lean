def Road : Type := String
def Direction : Type := String

-- <vc-helpers>
-- </vc-helpers>

def reverse_directions (directions : List Direction) : List Direction := sorry

theorem reverse_directions_length {directions : List Direction} :
  directions ≠ [] →
  (reverse_directions directions).length = directions.length
  := sorry

theorem reverse_directions_begin {directions : List Direction} :
  directions ≠ [] →
  (reverse_directions directions).head?.map (String.startsWith · "Begin") = some true
  := sorry

theorem reverse_directions_contains_substring {directions : List Direction} :
  directions ≠ [] →
  ∀ d ∈ reverse_directions directions, ∃ p, d.get ⟨p⟩ = 'o' ∧ d.get ⟨p+1⟩ = 'n'
  := sorry

theorem reverse_directions_involution {directions : List Direction} :
  directions ≠ [] →
  reverse_directions (reverse_directions directions) = directions
  := sorry

theorem reverse_directions_flips_turns {directions : List Direction} {d : Direction} :
  directions ≠ [] →
  d ∈ directions.tail →
  String.startsWith d "Left" →
  ∃ d' ∈ (reverse_directions directions).tail,
    String.startsWith d' "Right"
  := sorry

theorem reverse_directions_single :
  reverse_directions ["Begin on Road A"] = ["Begin on Road A"]
  := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval reverse_directions ["Begin on Road A", "Right on Road B", "Right on Road C", "Left on Road D"]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval reverse_directions ["Begin on Old Madras Road", "Left on Domlur Flyover", "Left on 100 Feet Road", "Right on Sarjapur Road", "Right on Hosur Road", "Right on Ganapathi Temple Road"]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible