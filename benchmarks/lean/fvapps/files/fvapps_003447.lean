-- <vc-preamble>
def getNth (s : String) (n : Nat) : Char := s.data.get! n

class NonString (α : Type)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse_it {α : Type} (x : α) : α :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_it_string_length {s : String} :
  String.length (reverse_it s) = String.length s :=
sorry

theorem reverse_it_string_reverses {s : String} {i : Nat} (h : i < String.length s) :
  getNth (reverse_it s) i = getNth s (String.length s - 1 - i) :=
sorry

theorem reverse_it_non_string_identity {α : Type} [NonString α] (x : α) :
  reverse_it x = x :=
sorry
-- </vc-theorems>