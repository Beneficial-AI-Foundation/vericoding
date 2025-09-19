-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_char (s : String) (c : Char) : Nat :=
sorry

def take_prefix (s : String) (n : Nat) : String :=
sorry

def is_balanced (s : String) (caps : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_char_caps_balance
  (s : String)
  (h : s.length > 0) :
  is_balanced s "xx" = ((count_char s 'x') % 2 = 0) :=
sorry

theorem empty_caps_always_balanced
  (s : String) :
  is_balanced s "" = true :=
sorry

theorem standard_parens_properties
  (s : String)
  (h : is_balanced s "()") :
  (count_char s '(' = count_char s ')') ∧
  ∀ (p : Nat), p ≤ s.length →
    count_char (take_prefix s p) '(' ≥ count_char (take_prefix s p) ')' :=
sorry
-- </vc-theorems>