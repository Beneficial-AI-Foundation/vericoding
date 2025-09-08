/-
Everyone loves short problem statements.
Given a function $ f(x) $ find its minimum value over the range $ 0 < x < π/2$
$
f(x) = ( x^2 + b*x + c ) / sin( x )
$

-----Input:-----
- First-line will contain $T$, the number of test cases. Then the test cases follow. 
- Each test case contains a single line of input, two real numbers $b, c$. 

-----Output:-----
For each test case, output the minimum value of $ f(x) $ over the given range. Absolute error of $10^{-6}$ is allowed.

-----Constraints-----
- $1 \leq T \leq 100000$
- $1 \leq b,c \leq 20$

-----Sample Input:-----
1
2 2

-----Sample Output:-----
5.8831725615
-/

-- <vc-helpers>
-- </vc-helpers>

def find_min_fx (b c : Float) : Float :=
  sorry

theorem find_min_fx_is_finite (b c : Float) :
  let result := find_min_fx b c
  Float.isFinite result := by sorry

theorem find_min_fx_is_minimum (b c : Float) :
  let result := find_min_fx b c
  let fx := fun (x : Float) => (x^2 + b*x + c)/Float.sin x
  ∀ x, 0 < x ∧ x < 3.14159 → result ≤ fx x + 0.000001 := by sorry 

theorem find_min_fx_positive_inputs (b c : Float) :
  0.1 ≤ b ∧ b ≤ 10 →
  0.1 ≤ c ∧ c ≤ 10 →
  0 < find_min_fx b c := by sorry

theorem find_min_fx_known_value :
  Float.abs (find_min_fx 2 2 - 5.8831725615) < 0.000001 := by sorry

-- Apps difficulty: interview
-- Assurance level: guarded