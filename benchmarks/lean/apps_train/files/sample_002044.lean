You are given a Young diagram. 

Given diagram is a histogram with $n$ columns of lengths $a_1, a_2, \ldots, a_n$ ($a_1 \geq a_2 \geq \ldots \geq a_n \geq 1$). [Image] Young diagram for $a=[3,2,2,2,1]$. 

Your goal is to find the largest number of non-overlapping dominos that you can draw inside of this histogram, a domino is a $1 \times 2$ or $2 \times 1$ rectangle.

-----Input-----

The first line of input contain one integer $n$ ($1 \leq n \leq 300\,000$): the number of columns in the given histogram.

The next line of input contains $n$ integers $a_1, a_2, \ldots, a_n$ ($1 \leq a_i \leq 300\,000, a_i \geq a_{i+1}$): the lengths of columns.

-----Output-----

Output one integer: the largest number of non-overlapping dominos that you can draw inside of the given Young diagram.

-----Example-----
Input
5
3 2 2 2 1

Output
4

-----Note-----

Some of the possible solutions for the example:

[Image] $\square$

def solve_dominos (n : Nat) (arr : List Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
