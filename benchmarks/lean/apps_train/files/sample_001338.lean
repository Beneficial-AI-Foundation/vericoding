In this problem the input will consist of a number of lines of English text consisting of the letters of the English alphabet, the punctuation marks ' (apostrophe), . (full stop), , (comma), ; (semicolon), :(colon) and white space characters (blank, newline). Your task is print the words in the text in reverse order without any punctuation marks.
For example consider the following candidate for the input text:
$ $
This is a sample piece of text to illustrate this 
problem.  If you are smart you will solve this right.

$ $
The corresponding output would read as:
$ $
right this solve will you smart are you If problem
this illustrate to text of piece sample a is This

$ $
That is, the lines are printed in reverse order and in each line the words are printed in reverse order.

-----Input:-----
The first line of input contains a single integer $N$, indicating the number of lines in the input. This is followed by $N$ lines of input text.

-----Output:-----
$N$ lines of output text containing the input lines in reverse order and where each line contains the words in reverse order as illustrated above.

-----Constraints:-----
- $1 \leq N \leq 10000$.
- There are at most $80$ characters in each line

-----Sample input-----
2
This is a sample piece of text to illustrate this 
problem.  If you are smart you will solve this right.

-----Sample output-----
right this solve will you smart are you If problem
this illustrate to text of piece sample a is This

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded