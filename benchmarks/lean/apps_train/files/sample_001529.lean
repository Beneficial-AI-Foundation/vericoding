Indian National Olympiad in Informatics 2012
You are given a table with 2 rows and N columns. Each cell has an integer in it. The score of such a table is defined as follows: for each column, consider the sum of the two numbers in the column; the maximum of the N numbers so obtained is the score. For example, for the table
7162
1234

the score is max(7 + 1, 1 + 2, 6 + 3, 2 + 4) = 9.

The first row of the table is fixed, and given as input. N possible ways to fill the second row are considered:
1,2,...,N
2,3,...,N,1
3,4,...,N,1,2
···
N, 1, ... , ,N − 1

For instance, for the example above, we would consider each of the following as possibilities for the second row.
1234
2341
3412
4123

Your task is to find the score for each of the above choices of the second row. In the example above, you would evaluate the following four tables,
7162 7162 7162 7162
1234 2341 3412 4123

and compute scores 9, 10, 10 and 11, respectively.

-----Input format -----
The first line of the input has a single integer, N. The second line of the input has N integers, representing the first row, from left to right.

-----Output format -----
The output should consist of a single line with N integers. For 1 ² k ² N, the kth number in the output should be the score when the second row of the table is taken to be k,k+1,...,N,1,...,k−1.

-----Test Data -----
The testdata is grouped into two subtasks with the following constraints on the inputs.
• Subtask 1 [30 points] : 1 ≤ N ≤ 3000.
• Subtask 2 [70 points] : 1 ≤ N ≤ 200000.
In both the subtasks, all the integers in the first row of the table are between 1 and 100000, inclusive.

-----Example -----
Here is the sample input and output corresponding to the example above.

-----Sample input -----
4
7 1 6 2

-----Sample output-----
9 10 10 11

Note: Your program should not print anything other than what is specified in the output format. Please remove all diagnostic print statements before making your final submission. A program with extraneous output will be treated as incorrect!

def max_list (l: List Int) : Int :=
  match l with
  | [] => 0
  | h::t => (List.foldl max h t)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
