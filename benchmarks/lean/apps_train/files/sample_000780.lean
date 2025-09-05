Chef has provided with a sequence of integers of length $N$ arranged in an unsorted fashion.
The elements of the sequence are ordered as ${A1,A2,A3.....A'N}$
The task of the chef is to identify the highest and lowest value among the given sequence. It is assured that the sequence given contains the highest and the lowest value always
Please help chef in finding the desired value.

-----Input:-----
- First line will contain $N$, number of elements in the sequence.  
- Next line contains  $N$ integers of the sequence  . 

-----Output:-----
Print the HIGHEST and  LOWEST value of the sequence respectively.

-----Constraints-----
- $1 \leq N \leq 100$
- $2 \leq  {A1,A2,A3.....A'N}  \leq 10^4$

-----Sample Input:-----
5
3 2 7 9 4

-----Sample Output:-----
9 2

-----EXPLANATION:-----
This list is :
[3,2,7,9,4]  so the highest value is 9 and lowest is 2 respectively.

def find_max_min (n : Nat) (seq : String) : Int × Int := sorry

def maximum : List Int → Int := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible