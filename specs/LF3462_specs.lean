-- <vc-preamble>
def sum_list : List Nat → Nat
  | [] => 0
  | x::xs => x + sum_list xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def aa_percentage (seq : String) (residues : List Char := ['A', 'I', 'L', 'M', 'F', 'W', 'Y', 'V']) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem default_residues_in_bounds (seq : String)
  (h : ∀ c ∈ seq.data, c ∈ ['A','C','D','E','F','G','H','I','K','L','M','N','P','Q','R','S','T','V','W','Y']) :
  0 ≤ aa_percentage seq ∧ aa_percentage seq ≤ 100 :=
sorry

theorem custom_residues_in_bounds (seq : String) (residues : List Char)
  (h1 : ∀ c ∈ seq.data, c ∈ ['A','C','D','E','F','G','H','I','K','L','M','N','P','Q','R','S','T','V','W','Y'])
  (h2 : ∀ c ∈ residues, c ∈ ['A','C','D','E','F','G','H','I','K','L','M','N','P','Q','R','S','T','V','W','Y'])
  (h3 : residues.Nodup) :
  0 ≤ aa_percentage seq residues ∧ aa_percentage seq residues ≤ 100 :=
sorry

theorem empty_residues_gives_zero (seq : String)
  (h : ∀ c ∈ seq.data, c ∈ ['A','C','D','E','F','G','H','I','K','L','M','N','P','Q','R','S','T','V','W','Y']) :
  aa_percentage seq [] = 0 :=
sorry

theorem residue_count_matches (seq : String) (residues : List Char)
  (h1 : ∀ c ∈ seq.data, c ∈ ['A','C','D','E','F','G','H','I','K','L','M','N','P','Q','R','S','T','V','W','Y'])
  (h2 : ∀ c ∈ residues, c ∈ ['A','C','D','E','F','G','H','I','K','L','M','N','P','Q','R','S','T','V','W','Y'])
  (h3 : residues.Nodup) :
  aa_percentage seq residues =
    ((sum_list (residues.map (λ r => seq.data.count r))) * 100 + seq.length / 2) / seq.length :=
sorry

theorem default_residues_consistent (seq : String)
  (h : ∀ c ∈ seq.data, c ∈ ['A','C','D','E','F','G','H','I','K','L','M','N','P','Q','R','S','T','V','W','Y']) :
  aa_percentage seq = aa_percentage seq ['A', 'I', 'L', 'M', 'F', 'W', 'Y', 'V'] :=
sorry
-- </vc-theorems>