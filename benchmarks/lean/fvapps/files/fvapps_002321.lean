-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isUppercase (c : Char) : Bool :=
sorry

def toCharList (s : String) : List Char :=
sorry

def removeDashes (s : String) : String :=
sorry

def licenseKeyFormatting (s : String) (k : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem license_key_uppercase (s : String) (k : Nat) :
  ∀ c ∈ toCharList (licenseKeyFormatting s k), isUppercase c = true
  :=
sorry

theorem license_key_same_length (s : String) (k : Nat) :
  String.length (removeDashes (licenseKeyFormatting s k)) =
  String.length (removeDashes s)
  :=
sorry

theorem license_key_group_sizes (s : String) (k : Nat) :
  let result := licenseKeyFormatting s k
  let groups := String.splitOn result "-"
  groups.length ≤ 1 ∨
  (∀ g ∈ groups.tail, String.length g = k) ∧ String.length groups.head! ≤ k
  :=
sorry

theorem license_key_empty (k : Nat) :
  licenseKeyFormatting "" k = ""
  :=
sorry

theorem license_key_single_dash (k : Nat) :
  licenseKeyFormatting "-" k = ""
  :=
sorry

theorem license_key_no_dashes (s : String) (k : Nat) :
  (∀ c ∈ toCharList s, c ≠ '-') →
  removeDashes (licenseKeyFormatting s k) = String.mk (List.map Char.toUpper (toCharList s))
  :=
sorry
-- </vc-theorems>