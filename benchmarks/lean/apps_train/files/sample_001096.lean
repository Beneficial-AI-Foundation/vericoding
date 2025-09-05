Shivam is working on electric circuits. He requires some connecting wires. He needs to make a total of N connections and he has mentioned his wire length requirements for each connection in an integer sequence A. For buying wires, he need to decide the length of each wire piece, and he’ll get as many wire pieces of the chosen length each at unit cost (cost 1 per piece) but he can't get wires of different lengths. Also, he can't cut wire pieces to make new pieces of different (smaller) length(s).
But he can connect any number of wires together to form a new single wire piece whose length is the sum of lengths of the wires connected. So, Shivam needs to choose an integer length for buying wires. Shivam hates to waste anything, and he hates it even more if that thing is money.
Shivam is weak in mathematics and is asking you to help him in this situation. Help him decide the length of wires and total number of wires so as to minimize the total expenditure.
Note: You cannot make a connection which requires a wire piece of length X with a wire piece of length Y if X≠Y.
Input:
·        The first line of the input contains T = Number of Test cases
·        The first line of each test case contains an integer N
·        The second line contains N space separated integers A1, A2, …., AN.
Output:
For each test case print a single line containing two space separated integers, length of each wire and the corresponding minimum cost.
Constraints:
·       1 <= T <= 10
·       1 <= N <= 10^5
·        1 <= Ai <= 10^5, for each valid i
Sample Input:
1
3
2 4 8
Sample Output:
2 7

def List.sum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: xs => x + xs.sum

def gcd (a b : Nat) : Nat :=
  sorry

def gcd_list (nums : List Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded