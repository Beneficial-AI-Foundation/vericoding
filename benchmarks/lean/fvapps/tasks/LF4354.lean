-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def perms (s : String) : Nat :=
sorry

def listPerms (l : List α) : List (List α) :=
sorry

def listToString (l : List Char) : String :=
sorry

def numUnique (xs : List String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem perms_matches_unique_perms_int {n : Nat} :
  perms (toString n) = numUnique ((listPerms (toString n).data).map listToString) :=
sorry

theorem perms_matches_unique_perms_str {s : String} :
  perms s = numUnique ((listPerms s.data).map listToString) :=
sorry

theorem perms_order_invariant {n : Nat} :
  perms (toString n) = perms (toString n) :=
sorry

theorem perms_positive_int {s : String} (h : s.length > 0) :
  perms s > 0 :=
sorry

theorem perms_single_char {c : Char} :
  perms (String.mk [c]) = 1 :=
sorry
-- </vc-theorems>