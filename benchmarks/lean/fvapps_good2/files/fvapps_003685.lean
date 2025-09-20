-- <vc-preamble>
def isStopCodon (codon : String) : Bool :=
  codon = "UAA" || codon = "UAG" || codon = "UGA"

def charsToCodon (chars : List Char) : String :=
  String.mk chars

def groupsOf3 (xs : List α) : List (List α) :=
  match xs with
  | [] => []
  | x₁::xs₁ => match xs₁ with
    | [] => [[x₁]]
    | x₂::xs₂ => match xs₂ with
      | [] => [[x₁, x₂]]
      | x₃::xs₃ => [x₁, x₂, x₃]::(groupsOf3 xs₃)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def protein (rna : String) : String := sorry

def validCodon (c : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem protein_length_le_input_div_3 {rna : String} (h : protein rna ≠ "") :
  (protein rna).length ≤ rna.length / 3 :=
sorry

theorem protein_valid_acids {rna : String} (h : protein rna ≠ "") :
  ∀ c, c ∈ (protein rna).data →
    c ∈ ['F', 'L', 'I', 'M', 'V', 'S', 'P', 'T', 'A', 'G', 'Y', 'C', 'H', 'N', 'K', 'D', 'E', 'Q', 'W', 'R', 'G'] :=
sorry

theorem protein_stops_at_first_stop {rna : String} (h : protein rna ≠ "") :
  let codons := (rna.data.take (rna.length / 3 * 3)) |> groupsOf3 |>.map charsToCodon
  let firstStop := match List.findIdx? isStopCodon codons with
    | none => codons.length
    | some n => n
  (protein rna).length ≤ firstStop :=
sorry

theorem protein_returns_string_length {rna : String} (h : ∀ c, c ∈ rna.data → c ∈ ['A', 'U', 'G', 'C']) :
  protein rna ≠ "" → (protein rna).length ≤ rna.length / 3 :=
sorry
-- </vc-theorems>