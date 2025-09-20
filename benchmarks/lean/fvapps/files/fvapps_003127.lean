-- <vc-preamble>
def DnaBases : List Char := ['A', 'C', 'G', 'T']

def isValidDnaChar (c : Char) : Bool :=
  match DnaBases.find? (· == c) with
  | some _ => true
  | none => false

def isValidDnaString (s : String) : Bool :=
  match s.data.find? (fun c => !isValidDnaChar c) with
  | some _ => false
  | none => true
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def motif_locator (sequence motif : String) : List Nat :=
sorry

def substring (s : String) (start len : Nat) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem motif_positions_valid (sequence motif : String)
  (h1 : isValidDnaString sequence)
  (h2 : isValidDnaString motif) :
  let positions := motif_locator sequence motif
  (∀ p ∈ positions, 0 < p ∧ p ≤ sequence.length) ∧
  (∀ p ∈ positions, substring sequence (p-1) motif.length = motif) :=
sorry

theorem positions_ordered_nonoverlap (sequence motif : String)
  (h1 : isValidDnaString sequence)
  (h2 : isValidDnaString motif) :
  let positions := motif_locator sequence motif
  (∀ i j, i < j → j < positions.length → positions[i]! ≤ positions[j]!) ∧
  (∀ i, i < positions.length - 1 → positions[i+1]! - positions[i]! ≥ motif.length) :=
sorry

theorem empty_sequence (motif : String)
  (h : isValidDnaString motif) :
  motif_locator "" motif = [] :=
sorry

theorem motif_longer_than_seq :
  motif_locator "ACG" "ACGT" = [] :=
sorry
-- </vc-theorems>