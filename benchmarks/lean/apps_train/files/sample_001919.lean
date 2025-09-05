The Little Elephant has an integer a, written in the binary notation. He wants to write this number on a piece of paper.

To make sure that the number a fits on the piece of paper, the Little Elephant ought to delete exactly one any digit from number a in the binary record. At that a new number appears. It consists of the remaining binary digits, written in the corresponding order (possible, with leading zeroes).

The Little Elephant wants the number he is going to write on the paper to be as large as possible. Help him find the maximum number that he can obtain after deleting exactly one binary digit and print it in the binary notation.

-----Input-----

The single line contains integer a, written in the binary notation without leading zeroes. This number contains more than 1 and at most 10^5 digits.

-----Output-----

In the single line print the number that is written without leading zeroes in the binary notation — the answer to the problem.

-----Examples-----
Input
101

Output
11

Input
110010

Output
11010

-----Note-----

In the first sample the best strategy is to delete the second digit. That results in number 11_2 = 3_10.

In the second sample the best strategy is to delete the third or fourth digits — that results in number 11010_2 = 26_10.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded