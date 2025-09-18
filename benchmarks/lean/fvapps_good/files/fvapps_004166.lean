-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def freq_seq (s : String) (sep : String) : String := sorry 

def String.count (s : String) (c : Char) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem freq_seq_length {s sep : String} (h1 : s.length > 0) (h2 : sep.length = 1) :
  (freq_seq s sep).length > 0 := sorry

theorem freq_seq_counts {s sep : String} (h1 : s.length > 0) (h2 : sep.length = 1) 
  (i : Nat) (hi : i < s.length) :
  let c := s.data[i]
  s.count c > 0 := sorry

theorem freq_seq_nonneg {s sep : String} (h1 : s.length > 0) (h2 : sep.length = 1) :
  ∀ c : Char, c ∈ s.data → s.count c ≥ 0 := sorry

theorem freq_seq_deterministic {s sep : String} (h1 : s.length > 0) (h2 : sep.length = 1) :
  freq_seq s sep = freq_seq s sep := sorry
-- </vc-theorems>