def isUpper (c : Char) : Bool := sorry
def isLower (c : Char) : Bool := sorry

def countUpper (s : String) : Nat := sorry
def countLower (s : String) : Nat := sorry

inductive MessageType where
  | chef
  | brother  
  | both
  | none
  deriving Repr

-- <vc-helpers>
-- </vc-helpers>

def classify_message (N : Nat) (K : Nat) (s : String) : MessageType := sorry

theorem classify_message_properties {N K : Nat} {s : String} :
  let upper := countUpper s
  let lower := countLower s
  match classify_message N K s with
  | MessageType.chef => lower > K ∧ upper ≤ K 
  | MessageType.brother => upper > K ∧ lower ≤ K
  | MessageType.both => upper ≤ K ∧ lower ≤ K
  | MessageType.none => upper > K ∧ lower > K
  := sorry

theorem all_upper {N : Nat} (h : N > 0) :
  classify_message N (N-1) (String.mk (List.replicate N 'A')) = MessageType.brother := sorry

theorem all_lower {N : Nat} (h : N > 0) :
  classify_message N (N-1) (String.mk (List.replicate N 'a')) = MessageType.chef := sorry

theorem empty_k_large {N : Nat} (h : N > 1) {s : String} :
  classify_message N 0 s = MessageType.none := sorry

theorem empty_k_small {N : Nat} (h : N = 1) {s : String} :
  classify_message N 0 s ≠ MessageType.none := sorry

/-
info: 'chef'
-/
-- #guard_msgs in
-- #eval classify_message 5 1 "frauD"

/-
info: 'brother'
-/
-- #guard_msgs in
-- #eval classify_message 5 1 "FRAUD"

/-
info: 'both'
-/
-- #guard_msgs in
-- #eval classify_message 4 4 "Life"

-- Apps difficulty: interview
-- Assurance level: unguarded