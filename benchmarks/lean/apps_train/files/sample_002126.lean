Rudolf is on his way to the castle. Before getting into the castle, the security staff asked him a question:

Given two binary numbers $a$ and $b$ of length $n$. How many different ways of swapping two digits in $a$ (only in $a$, not $b$) so that bitwise OR of these two numbers will be changed? In other words, let $c$ be the bitwise OR of $a$ and $b$, you need to find the number of ways of swapping two bits in $a$ so that bitwise OR will not be equal to $c$.

Note that binary numbers can contain leading zeros so that length of each number is exactly $n$.

Bitwise OR is a binary operation. A result is a binary number which contains a one in each digit if there is a one in at least one of the two numbers. For example, $01010_2$ OR $10011_2$ = $11011_2$.

Well, to your surprise, you are not Rudolf, and you don't need to help him$\ldots$ You are the security staff! Please find the number of ways of swapping two bits in $a$ so that bitwise OR will be changed.

-----Input-----

The first line contains one integer $n$ ($2\leq n\leq 10^5$) — the number of bits in each number.

The second line contains a binary number $a$ of length $n$.

The third line contains a binary number $b$ of length $n$.

-----Output-----

Print the number of ways to swap two bits in $a$ so that bitwise OR will be changed.

-----Examples-----
Input
5
01011
11001

Output
4

Input
6
011000
010011

Output
6

-----Note-----

In the first sample, you can swap bits that have indexes $(1, 4)$, $(2, 3)$, $(3, 4)$, and $(3, 5)$.

In the second example, you can swap bits that have indexes $(1, 2)$, $(1, 3)$, $(2, 4)$, $(3, 4)$, $(3, 5)$, and $(3, 6)$.

def countValidBitSwaps (n : Nat) (a : String) (b : String) : Nat :=
  sorry

def stringRepeat (s : String) (n : Nat) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded