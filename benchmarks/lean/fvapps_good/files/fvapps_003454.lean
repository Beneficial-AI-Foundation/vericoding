-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse_complement (s : String) : String := sorry

theorem valid_dna_properties {dna : String}
  (h : ∀ c ∈ dna.data, c = 'A' ∨ c = 'T' ∨ c = 'C' ∨ c = 'G') :
  let result := reverse_complement dna
  -- Result only contains valid nucleotides
  (∀ c ∈ result.data, c = 'A' ∨ c = 'T' ∨ c = 'C' ∨ c = 'G') ∧
  -- Length preserved 
  result.length = dna.length ∧
  -- Complement relations hold (stated more abstractly without indexed access)
  (∀ c ∈ dna.data, 
    match c with
    | 'A' => 'T' ∈ result.data
    | 'T' => 'A' ∈ result.data
    | 'C' => 'G' ∈ result.data
    | 'G' => 'C' ∈ result.data
    | _ => True) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_dna_result {dna : String}
  (h : ∃ c ∈ dna.data, c ≠ 'A' ∧ c ≠ 'T' ∧ c ≠ 'C' ∧ c ≠ 'G') :
  reverse_complement dna = "Invalid sequence" := sorry

theorem empty_sequence :
  reverse_complement "" = "" := sorry

theorem reverse_twice_identity {dna : String}
  (h : ∀ c ∈ dna.data, c = 'A' ∨ c = 'T' ∨ c = 'C' ∨ c = 'G') :
  reverse_complement (reverse_complement dna) = dna.toUpper := sorry

theorem case_insensitive {dna : String}
  (h : ∀ c ∈ dna.data, c.toLower = 'a' ∨ c.toLower = 't' ∨ c.toLower = 'c' ∨ c.toLower = 'g') :
  reverse_complement dna = reverse_complement dna.toUpper := sorry
-- </vc-theorems>