Two words rhyme if their last 3 letters are a match. Given N words, print the test case number (of the format Case : num) followed by the rhyming words in separate line adjacent to each other.

The output can be in anyorder.

-----Input-----
First line contains the number of test case T

The next line contains the number of words N

Next N words follow . They’ll contain only alphabets from ‘a’-‘z’.

-----Output-----
Print case number (for each test case) of the format Case : num followed by the words that rhyme in a new line.

-----Constraints-----
1 <= T <= 5

1 <= N <= 1000

3 <= length of each word <= 1000

-----Example-----
Input:
3
3
nope qwerty hope
5 
brain drain request grain nest
4
these words dont rhyme

Output:
Case : 1
hope nope
qwerty
Case : 2
brain drain grain
nest request
Case : 3
these
dont
words
rhyme

-----Explanation-----
Case : 2

brain drain grain

nest request

Case : 3

these

dont

words

rhyme
Explanation for case 1: since hope and nope rhyme (suffix “ope” matches), we print them in the same line and qwerty In a new line.

Note that

qwerty

nope hope

is also correct (the output can be in any order )

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
