Igor the analyst has adopted n little bunnies. As we all know, bunnies love carrots. Thus, Igor has bought a carrot to be shared between his bunnies. Igor wants to treat all the bunnies equally, and thus he wants to cut the carrot into n pieces of equal area. 

Formally, the carrot can be viewed as an isosceles triangle with base length equal to 1 and height equal to h. Igor wants to make n - 1 cuts parallel to the base to cut the carrot into n pieces. He wants to make sure that all n pieces have the same area. Can you help Igor determine where to cut the carrot so that each piece have equal area?

 [Image] Illustration to the first example. 

-----Input-----

The first and only line of input contains two space-separated integers, n and h (2 ≤ n ≤ 1000, 1 ≤ h ≤ 10^5).

-----Output-----

The output should contain n - 1 real numbers x_1, x_2, ..., x_{n} - 1. The number x_{i} denotes that the i-th cut must be made x_{i} units away from the apex of the carrot. In addition, 0 < x_1 < x_2 < ... < x_{n} - 1 < h must hold. 

Your output will be considered correct if absolute or relative error of every number in your output doesn't exceed 10^{ - 6}.

Formally, let your answer be a, and the jury's answer be b. Your answer is considered correct if $\frac{|a - b|}{\operatorname{max}(1, b)} \leq 10^{-6}$.

-----Examples-----
Input
3 2

Output
1.154700538379 1.632993161855

Input
2 100000

Output
70710.678118654752

-----Note-----

Definition of isosceles triangle: https://en.wikipedia.org/wiki/Isosceles_triangle.

def calculate_cuts (n: Nat) (h: Float) : Array Float := 
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded