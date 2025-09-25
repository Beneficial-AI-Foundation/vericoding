-- <vc-preamble>
def find_gatecrashers (party_members: List Int) (invitations: List (Int × List Int)) : List Int :=
  sorry

def is_sorted (l: List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l.get ⟨i, by sorry⟩ ≤ l.get ⟨j, by sorry⟩

def is_subset (l₁ l₂: List Int) : Prop :=
  ∀ x, x ∈ l₁ → x ∈ l₂
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def known_guests (invitations: List (Int × List Int)) : List Int :=
  let hosts := invitations.map Prod.fst
  let guests := (invitations.map Prod.snd).join
  hosts ++ guests
-- </vc-definitions>

-- <vc-theorems>
theorem find_gatecrashers_sorted (party_members: List Int) (invitations: List (Int × List Int)) :
  is_sorted (find_gatecrashers party_members invitations) :=
  sorry

theorem find_gatecrashers_subset (party_members: List Int) (invitations: List (Int × List Int)) :
  is_subset (find_gatecrashers party_members invitations) party_members :=
  sorry

theorem find_gatecrashers_not_invited (party_members: List Int) (invitations: List (Int × List Int)) :
  ∀ x ∈ find_gatecrashers party_members invitations, x ∉ known_guests invitations :=
  sorry

theorem find_gatecrashers_complete (party_members: List Int) (invitations: List (Int × List Int)) :
  ∀ x ∈ party_members, x ∉ known_guests invitations → x ∈ find_gatecrashers party_members invitations :=
  sorry

theorem find_gatecrashers_empty_invitations (party_members: List Int) :
  is_sorted (find_gatecrashers party_members []) ∧ 
  find_gatecrashers party_members [] = party_members :=
  sorry 

theorem find_gatecrashers_empty_party (invitations: List (Int × List Int)) :
  find_gatecrashers [] invitations = [] :=
  sorry

/-
info: [4]
-/
-- #guard_msgs in
-- #eval find_gatecrashers [0, 1, 2, 3, 4] [(0, [1, 2]), (2, [3])]

/-
info: []
-/
-- #guard_msgs in
-- #eval find_gatecrashers [0, 1, 2] [(0, [1]), (1, [2])]

/-
info: [0, 1, 2, 3]
-/
-- #guard_msgs in
-- #eval find_gatecrashers [0, 1, 2, 3] []
-- </vc-theorems>