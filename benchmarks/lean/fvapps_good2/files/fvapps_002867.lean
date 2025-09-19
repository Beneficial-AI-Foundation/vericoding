-- <vc-preamble>
inductive CardIssuer where
  | AMEX : CardIssuer
  | Discover : CardIssuer
  | Mastercard : CardIssuer
  | VISA : CardIssuer
  | Unknown : CardIssuer
deriving BEq

def CardIssuer.toString : CardIssuer → String
  | AMEX => "AMEX"
  | Discover => "Discover"
  | Mastercard => "Mastercard"
  | VISA => "VISA"
  | Unknown => "Unknown"
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_issuer (number : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem issuer_is_valid (n : Nat) :
  let result := get_issuer n
  result = "AMEX" ∨ result = "Discover" ∨ result = "Mastercard" ∨ result = "VISA" ∨ result = "Unknown" :=
sorry

theorem amex_rules (n : Nat) :
  let digits := n.repr
  (digits.take 2 = "34" ∨ digits.take 2 = "37") → get_issuer n = "AMEX" ∧
  (digits.take 2 = "35" ∨ digits.take 2 = "36") → get_issuer n = "Unknown" :=
sorry

theorem visa_length_rules (n : Nat) :
  let digits := n.repr
  (digits.get! 0 = '4' ∧ (digits.length = 13 ∨ digits.length = 16)) →
    get_issuer n = "VISA" ∧
  (digits.get! 0 = '4' ∧ ¬(digits.length = 13 ∨ digits.length = 16)) →
    get_issuer n = "Unknown" :=
sorry

theorem mastercard_rules (n : Nat) :
  let digits := n.repr
  (digits.take 2 = "51" ∨ digits.take 2 = "52" ∨ digits.take 2 = "53" ∨ digits.take 2 = "54" ∨ digits.take 2 = "55") →
  digits.length = 16 →
  get_issuer n = "Mastercard" :=
sorry

theorem discover_rules (n : Nat) :
  let digits := n.repr
  digits.startsWith "6011" ∧ digits.length = 16 →
    get_issuer n = "Discover" :=
sorry
-- </vc-theorems>