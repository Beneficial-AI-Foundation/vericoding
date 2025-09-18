-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def protein_synthesis (dna_str: String) : List String := sorry

def valid_aas : List String := ["Ala", "Arg", "Asn", "Asp", "Cys", "Gln", "Glu", "Gly", "His", "Ile",
                               "Leu", "Lys", "Met", "Phe", "Pro", "Ser", "Thr", "Trp", "Tyr", "Val", "Stop"]

theorem output_structure {dna_str : String} (h : ∀ c ∈ dna_str.data, c ∈ ['A', 'C', 'G', 'T']) :
  let result := protein_synthesis dna_str
  result.length = 2 ∧ 
  (∀ c ∈ result[0]!.data, c ∈ ['A', 'U', 'C', 'G', ' ']) ∧
  (∀ aa ∈ result[1]!.splitOn " ", aa ∈ valid_aas) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dna_to_rna_conversion {dna_str : String} (h : ∀ c ∈ dna_str.data, c ∈ ['A', 'C', 'G', 'T']) :
  let result := protein_synthesis dna_str
  let rna := (result[0]!.replace " " "").data
  ∀ i, i < dna_str.length → 
    match dna_str.data[i]! with
    | 'A' => rna[i]! = 'U'
    | 'T' => rna[i]! = 'A'  
    | 'C' => rna[i]! = 'G'
    | 'G' => rna[i]! = 'C'
    | _ => True := sorry

theorem codon_spacing {dna_str : String} (h : ∀ c ∈ dna_str.data, c ∈ ['A', 'C', 'G', 'T']) :
  let result := protein_synthesis dna_str
  let rna_codons := result[0]!.splitOn " "
  (∀ i, i < rna_codons.length - 1 → (rna_codons[i]!).length = 3) ∧ 
  (rna_codons.length > 0 → 
   1 ≤ (rna_codons[rna_codons.length - 1]!).length ∧ 
   (rna_codons[rna_codons.length - 1]!).length ≤ 3) := sorry

theorem translation_consistency {dna_str : String} (h : ∀ c ∈ dna_str.data, c ∈ ['A', 'C', 'G', 'T']) :
  let result := protein_synthesis dna_str
  let rna_codons := result[0]!.splitOn " "
  let aas := result[1]!.splitOn " "
  ∀ i j, i < rna_codons.length → j < rna_codons.length →
    rna_codons[i]!.length = 3 → 
    rna_codons[j]!.length = 3 →
    rna_codons[i]! = rna_codons[j]! → 
    aas[i]! = aas[j]! := sorry
-- </vc-theorems>