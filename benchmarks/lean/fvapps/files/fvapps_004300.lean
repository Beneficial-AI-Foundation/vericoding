-- <vc-preamble>
def isBinary (n : Nat) : Bool :=
  n == 0 || n == 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gray2bin (bits : List Nat) : List Nat := sorry

def bin2gray (bits : List Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gray_code_roundtrip (bits : List Nat) (h : ∀ x ∈ bits, isBinary x = true) :
  gray2bin (bin2gray bits) = bits :=
sorry

theorem gray_code_length (bits : List Nat) (h₁ : List.length bits > 0) (h₂ : ∀ x ∈ bits, isBinary x = true) :
  List.length (bin2gray bits) = List.length bits :=
sorry

theorem gray_code_first_bit (bits : List Nat) (h₁ : List.length bits > 0) (h₂ : ∀ x ∈ bits, isBinary x = true) :
  List.head! (bin2gray bits) = List.head! bits :=
sorry

theorem gray_code_values_binary (bits : List Nat) (h₁ : List.length bits > 0) (h₂ : ∀ x ∈ bits, isBinary x = true) :
  ∀ x ∈ bin2gray bits, isBinary x = true :=
sorry
-- </vc-theorems>