-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encode (n : Nat) (s : String) : String :=
sorry

def decode (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encode_decode_roundtrip (n : Nat) (text : String) :
  decode (encode n text) = text :=
sorry

theorem encode_starts_with_n (n : Nat) (text : String) :
  List.get! (String.splitOn (encode n text) " ") 0 = toString n :=
sorry

theorem empty_string_case1 : decode (encode 5 "") = "" :=
sorry

theorem empty_string_case2 : encode 0 "" = "0 " :=
sorry
-- </vc-theorems>