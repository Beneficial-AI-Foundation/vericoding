In genetics 2 differents DNAs sequences can code for the same protein. 

This is due to the redundancy of the genetic code, in fact 2 different tri-nucleotide can code for the same amino-acid.
For example the tri-nucleotide 'TTT' and the tri-nucleotide 'TTC' both code for the amino-acid 'F'. For more information you can take a look [here](https://en.wikipedia.org/wiki/DNA_codon_table).

Your goal in this kata is to define if two differents DNAs sequences code for exactly the same protein. Your function take the 2 sequences you should compare.
For some kind of simplicity here the sequences will respect the following rules:

- It is a full protein sequence beginning with a Start codon and finishing by an Stop codon
- It will only contain valid tri-nucleotide. 

The translation hash is available for you under a translation hash `$codons` [Ruby] or `codons` [Python and JavaScript].

To better understand this kata you can take a look at this [one](https://www.codewars.com/kata/5708ef48fe2d018413000776), it can help you to start.

def code_for_same_protein (seq1 : String) (seq2 : String) : Bool := sorry

theorem identical_sequences_match
  (seq : String) :
  code_for_same_protein seq seq = true := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
