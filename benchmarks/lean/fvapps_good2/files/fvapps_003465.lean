-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def seqR : String → Bool :=
  sorry

def seqB : String → Bool :=
  sorry

def button_sequences (r : String) (b : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem button_sequences_valid_chars (r b : String) (h : r.length > 0 ∧ b.length > 0) :
  ∀ c, c ∈ (button_sequences r b).toList → c = 'R' ∨ c = 'B' :=
sorry

theorem button_sequences_length (r b : String) (h : r.length > 0 ∧ b.length > 0) :
  (button_sequences r b).length ≤ min r.length b.length :=
sorry

theorem button_sequences_all_zeros_red (s : String) (h : s.length > 0) :
  let zeros := String.mk (List.replicate s.length '0')
  ∀ c, c ∈ (button_sequences s zeros).toList → c = 'R' :=
sorry

theorem button_sequences_all_zeros_blue (s : String) (h : s.length > 0) :
  let zeros := String.mk (List.replicate s.length '0')
  ∀ c, c ∈ (button_sequences zeros s).toList → c = 'B' :=
sorry
-- </vc-theorems>