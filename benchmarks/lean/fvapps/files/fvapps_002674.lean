-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def send (s : String) : String := sorry
def receive (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encoding_decoding_roundtrip {s : String}
  (h : s.length > 0 ∧ s.length ≤ 100) :
  receive (send s) = s := sorry

theorem send_format {s : String} 
  (h : s.length > 0 ∧ s.length ≤ 100) :
  let encoded := send s
  let segments := encoded.split (· = ' ')
  (∀ seg ∈ segments, (seg.startsWith "0" ∨ seg.startsWith "00")) ∧ 
  (∀ c ∈ encoded.data, c = '0' ∨ c = ' ') := sorry 

theorem encoded_length_relationship {s : String}
  (h : s.length > 0 ∧ s.length ≤ 100) :
  (send s).length ≥ s.length := sorry

theorem receive_handles_valid_format {s : String}
  (h : s.length > 0) 
  (h₂ : ∀ c ∈ s.data, c = '0' ∨ c = ' ') :
  (receive s).length > 0 := sorry
-- </vc-theorems>