In this problem the input will consist of a number of lines of English text consisting of the letters of the English alphabet, the punctuation marks ' (apostrophe), . (full stop), , (comma), ; (semicolon), :(colon) and white space characters (blank, newline).
Your task is print the words in the text in lexicographic order (that is, dictionary order). Each word should appear exactly once in your list. You can ignore the case (for instance, "The" and "the" are to be treated as the same word). There should be no uppercase letters in the output.
For example, consider the following candidate for the input text: 
This is a sample piece of text to illustrate this 
problem.

The corresponding output would read as:
a
illustrate
is
of
piece
problem
sample
text
this
to

-----Input format-----
- The first line of input contains a single integer $N$, indicating the number of lines in the input.
- This is followed by $N$ lines of input text.

-----Output format-----
- The first line of output contains a single integer $M$ indicating the number of distinct words in the given text. 
- The next $M$ lines list out these words in lexicographic order.

-----Constraints-----
- $1 \leq N \leq 10000$
- There are at most 80 characters in each line.
- There are at the most 1000 distinct words in the given text.

-----Sample Input-----
2
This is a sample piece of text to illustrate this 
problem. 

-----Sample Output-----
10
a
illustrate
is
of
piece
problem
sample
text
this
to

def process_text (lines : List String) : List String :=
  sorry

inductive List.LocalSorted : List String → Prop where
  | nil : List.LocalSorted []
  | single (x : String) : List.LocalSorted [x]
  | cons (x y : String) (rest : List String) 
    (h₁ : x ≤ y) (h₂ : List.LocalSorted (y::rest)) : 
    List.LocalSorted (x::y::rest)

inductive List.LocalNodup : List α → Prop where
  | nil : List.LocalNodup []
  | cons (x : α) (xs : List α) 
    (h₁ : x ∉ xs) (h₂ : List.LocalNodup xs) : 
    List.LocalNodup (x::xs)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded