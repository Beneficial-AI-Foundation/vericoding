DNA sequencing data can be stored in many different formats. In this Kata, we will be looking at SAM formatting. It is a plain text file where every line (excluding the first header lines) contains data about a "read" from whatever sample the file comes from. Rather than focusing on the whole read, we will take two pieces of information: the cigar string and the nucleotide sequence.

The cigar string is composed of numbers and flags. It represents how the read aligns to what is known as a reference genome. A reference genome is an accepted standard for mapping the DNA. 

The nucleotide sequence shows us what bases actually make up that section of DNA. They can be represented with the letters A, T, C, or G.

Example Read: ('36M', 'ACTCTTCTTGCGAAAGTTCGGTTAGTAAAGGGGATG')

The M in the above cigar string stands for "match", and the 36 stands for the length of the nucleotide sequence. Since all 36 bases are given the 'M' distinction, we know they all matched the reference.

Example Read: ('20M10S',  'ACTCTTCTTGCGAAAGTTCGGTTAGTAAAG')

In the above cigar string, only 20 have the "M" distinction, but the length of the actual string of nucleotides is 30. Therefore we know that read did not match the reference. (Don't worry about what the other letters mean. That will be covered in a later kata.)

Your job for this kata is to create a function that determines whether a cigar string fully matches the reference and accounts for all bases. If it does fully match, return True. If the numbers in the string do not match the full length of the string, return 'Invalid cigar'. If it does not fully match, return False.

*Note for C++: Return True, False, or Invalid cigar as strings*

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
