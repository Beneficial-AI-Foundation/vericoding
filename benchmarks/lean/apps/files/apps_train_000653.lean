/-
In my town ,there live a coder named Chef . He is a cool programmer . One day , he participate in a programming contest ,the contest give him only one problem . If he can’t solve the problem ,the problem setter will kill him . But the round allow you to help Chef. Can you save the life of Chef from problem setter ? :p
You are given two point of a straightline in X and Y axis and they are A(x1 , y1) and B(x2 ,y2) . Problem setter will give you another point C(x3 , y3) . If C exist in AB straightline ,then print “YES” . Otherwise ,print “NO” in first line and print the minimum distance from C to AB straightline in second line .
Please , save the life of Chef .
Note : It is not possible that A and B point is similar .

-----Input:-----
The first line of the input contains a single integer t (1≤t≤100) — the number of test cases .
Each test case starts with four integers( x1, y1 , x2 , y2 ) in first line .
Next line contains a single number q ,the number of queries . Each query contains two integers ( x3 ,y3 )

-----Output:-----
Print , q number of “YES” or “NO” (as it mentioned above) in each test case .For every test case , print “Test case : i ” ( 1<= i <=T )

-----Constraints-----
-1000 <=  x1 , y1 , x2 , y2 , x3 , y3 <= 1000

-----Sample Input:-----
2
3  5  6  5
2
4  5
6  8
3  4  7  10
1
7  4

-----Sample Output:-----
Test case : 1
YES
NO
3.000000
Test case : 2
NO
3.328201
-/

-- <vc-helpers>
-- </vc-helpers>

def String.toFloat? (s : String) : Option Float := sorry

def solve_geometry (x1 y1 x2 y2 : Int) (queries : List (Int × Int)) : List String :=
sorry

theorem solve_geometry_basic_properties {x1 y1 x2 y2 : Int} (h : x1 ≠ x2) 
  (queries : List (Int × Int)) :
  match solve_geometry x1 y1 x2 y2 queries with
  | result =>
    (result.length = queries.length ∨ result.length = 2 * queries.length) ∧
    ∀ i : Nat, i < result.length →
      if i % 2 = 0 
      then List.get! result i = "YES" ∨ List.get! result i = "NO"
      else ∃ d : Float, (List.get! result i).toFloat? = some d ∧ d ≥ 0 :=
sorry

-- Apps difficulty: interview
-- Assurance level: guarded