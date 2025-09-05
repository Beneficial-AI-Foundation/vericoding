For years you have been working hard in Santa's factory to manufacture gifts for kids in substandard work environments with no pay. You have finally managed to escape the factory and now you seek revenge. You are planning a heist with the Grinch to steal all the gifts which are locked in a safe. Since you have worked in the factory for so many years, you know how to crack the safe.
The passcode for the safe is an integer. This passcode keeps changing everyday, but you know a way to crack it. You will be given two numbers  A  and  B .
Passcode is the number of  X  such that 0 ≤ X < B and
gcd(A,B) = gcd(A+X,B).
Note : gcd(A,B) is the greatest common divisor of A & B.

-----Input-----
The first line contains the single integer T (1 ≤ T ≤ 50) — the number of test cases.
Next T lines contain test cases per line. Each line contains two integers  A  &  B 
( 1 ≤ A < B ≤ 1010 )

-----Output-----
Print T integers, one for each Test case. For each test case print the appropriate passcode for that day.

-----Sample Input-----
3
4 9
5 10
42 9999999967

-----Output-----
6
1
9999999966

def phi (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
