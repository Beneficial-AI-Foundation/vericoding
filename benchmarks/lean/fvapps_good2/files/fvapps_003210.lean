-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encrypt (text : Option String) (n : Int) : Option String :=
  sorry

def decrypt (text : Option String) (n : Int) : Option String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encrypt_decrypt_roundtrip {text : String} {n : Int} (h1 : text.length > 0) (h2 : n > 0) (h3 : n ≤ 10) :
  decrypt (encrypt (some text) n) n = some text :=
sorry

theorem encrypt_edge_cases {text : Option String} {n : Int} (h1 : text = none ∨ text = some "") (h2 : n > 0) (h3 : n ≤ 10) :
  encrypt text n = text :=
sorry

theorem encrypt_invalid_n {text : String} {n : Int} (h1 : text.length > 0) (h2 : n ≤ 0) :
  encrypt (some text) n = some text :=
sorry

theorem encrypt_length_preserved {text : String} {n : Int} (h1 : text.length > 0) (h2 : n > 0) (h3 : n ≤ 10) :
  (encrypt (some text) n).map String.length = some text.length :=
sorry

theorem encrypt_char_preservation {text : String} {n : Int} (h1 : text.length > 0) (h2 : n > 0) (h3 : n ≤ 10) :
  (encrypt (some text) n).map (fun s => s.data.toArray.qsort (· ≤ ·)) = some (text.data.toArray.qsort (· ≤ ·)) :=
sorry
-- </vc-theorems>