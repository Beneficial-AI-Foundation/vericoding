-- <vc-preamble>
def repeat_str (s : String) (n : Nat) : String :=
match n with
| 0 => ""
| n+1 => s ++ repeat_str s n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def code_for_same_protein (seq1 : String) (seq2 : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identical_sequences_match
  (seq : String) :
  code_for_same_protein seq seq = true :=
sorry

theorem different_length_no_match
  (n : Nat) :
  code_for_same_protein (repeat_str "ATG" n) (repeat_str "ATG" (n + 1)) = false :=
sorry

theorem different_length_sequences_no_match
  (seq1 seq2 : String) :
  seq1.length ≠ seq2.length →
  code_for_same_protein seq1 seq2 = false :=
sorry

theorem code_for_same_protein_reflexive
  (seq : String) :
  code_for_same_protein seq seq = true :=
sorry

theorem code_for_same_protein_symmetric
  (seq1 seq2 : String) :
  code_for_same_protein seq1 seq2 = true →
  code_for_same_protein seq2 seq1 = true :=
sorry
-- </vc-theorems>