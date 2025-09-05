You are a biologist working on the amino acid  composition of proteins. Every protein consists of a long chain of 20 different amino acids with different properties. 
Currently, you are collecting data on the percentage, various amino acids make up a protein you are working on. As manually counting the occurences of amino acids takes too long (especially when counting more than one amino acid), you decide to write a program for this task:

Write a function that takes two arguments,
 1. A (snippet of a) protein sequence
 2. A list of amino acid residue codes 

and returns the rounded percentage of the protein that the given amino acids make up. 
If no amino acid list is given, return the percentage of hydrophobic amino acid residues ["A", "I", "L", "M", "F", "W", "Y", "V"].

def aa_percentage (seq : String) (residues : List Char := ['A', 'I', 'L', 'M', 'F', 'W', 'Y', 'V']) : Nat := sorry

theorem default_residues_in_bounds (seq : String) 
  (h : ∀ c ∈ seq.data, c ∈ ['A','C','D','E','F','G','H','I','K','L','M','N','P','Q','R','S','T','V','W','Y']) :
  0 ≤ aa_percentage seq ∧ aa_percentage seq ≤ 100 := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded