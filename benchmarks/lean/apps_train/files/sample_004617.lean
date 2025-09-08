/-
# Find the gatecrashers on CocoBongo parties

CocoBongo is a club with very nice parties. However, you only can get inside if you know at least one other guest. Unfortunately, some gatecrashers can appear at those parties. The gatecrashers do not know any other party member and should not be at our amazing party!

We will give to you a collection with all party members and a collection with some guests and their invitations. Your mission is to find out those gatecrashers and give us a sorted array of them.

Note that invitations are undirectional relations, so if guest `A` invites `B`, we can consider that `B` also knows `A`. Once the relation `(A, {B})` appears on the invitations collection, the reverse relation `(B, {A})` may or may not appear in the input. You need to take care of that.

## Example

```python
party_members = [0,1,2,3,4]
invitations = [ (0, [1,2]), (2, [3]) ]
gatecrashers = [4]
```

## Explanation

We have `invitations = [ (0, [1,2]), (2, [3]) ]`.  
Guest `0` has invited guests `1` and `2`; also, guest `2` has invited guest `3`.
However, noone has invited guest `4`, so he is a gatecrasher.
-/

def find_gatecrashers (party_members: List Int) (invitations: List (Int × List Int)) : List Int :=
  sorry

def is_sorted (l: List Int) : Prop :=
  ∀ i j, i < j → j < l.length → l.get ⟨i, by sorry⟩ ≤ l.get ⟨j, by sorry⟩

def is_subset (l₁ l₂: List Int) : Prop :=
  ∀ x, x ∈ l₁ → x ∈ l₂

-- <vc-helpers>
-- </vc-helpers>

def known_guests (invitations: List (Int × List Int)) : List Int :=
  let hosts := invitations.map Prod.fst
  let guests := (invitations.map Prod.snd).join
  hosts ++ guests

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

-- Apps difficulty: introductory
-- Assurance level: guarded