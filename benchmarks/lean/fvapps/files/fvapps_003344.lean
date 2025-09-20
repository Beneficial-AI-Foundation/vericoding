-- <vc-preamble>
def DNA := String
def RNA := String
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dna_to_rna (dna: DNA) : RNA := sorry

theorem length_preserved (dna: DNA) :
  (dna_to_rna dna).length = dna.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem only_t_replaced (dna: DNA) (i: String.Pos) :
  let rna := dna_to_rna dna
  if dna.get i = 'T' then 
    rna.get i = 'U'
  else
    rna.get i = dna.get i := sorry

theorem valid_rna_chars (dna: DNA) (i: String.Pos) :
  (dna_to_rna dna).get i ∈ ['G', 'C', 'U', 'A'] := sorry

theorem idempotent (rna: RNA) (h: ∀ i: String.Pos, rna.get i ∈ ['G','C','U']) :
  dna_to_rna rna = rna := sorry
-- </vc-theorems>