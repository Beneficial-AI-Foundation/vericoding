Ravi is very good student in mathematics and he also like Even numbers very much .

On the other hand his friend Jhon like Odd numbers . Both of them are preparing for IIT JEE Advance .One day they are solving a  question together the question was Find the sum of first $n$ terms of the given series  $1^2+2.2^2+3^2+2.4^2+5^2+2.6^2+...........$
If the sum is odd then Jhon will be happy and will solve 2 more questions,and Ravi will not attempt more questions. If sum is even Ravi will  be happy and will solve 2 more questions and Jhon will not attempt more questions. 
So Your task is to decide who will solve more questions.

-----Input:-----
- First line will contain $n$, number of terms  in the given series.

-----Output:-----
Output single line "Ravi" if he solve more questions or "Jhon" if he solve more questions.

-----Constraints-----
- $1 \leq n \leq 100$

-----Sample Input:-----
2

3   

-----Sample Output:-----
Jhon       
Ravi       

-----EXPLANATION:-----
In the first test cases  sum of 2 terms is 9 (according to the given series) which is an odd number   so Jhon will solve 2 more questions and Ravi will not attempt more questions.
In second test case sum of 3 terms is 18 (according to the given series) which is an  even number according to the given series  so Ravi will solve 3 more questions and Jhon will not attempt more questions.

def seriesSumSolver (n : Nat) : String := sorry

theorem series_sum_solver_returns_valid_name (n : Nat) 
    (h : 1 ≤ n ∧ n ≤ 1000000) : 
    seriesSumSolver n = "Ravi" ∨ seriesSumSolver n = "Jhon" := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded