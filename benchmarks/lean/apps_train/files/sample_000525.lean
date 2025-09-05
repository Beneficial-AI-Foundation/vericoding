Bob has got some injury in his leg and due to this he can take exactly M steps in one move. 
Bob enters a square field of size NxN. The field is only having one gate(for both entrance and exit) at its one of the corners. Bob started walking along the perimeter of square field.(remember Bob can only take exactly M steps in one move and cannot reverse his direction of motion).
Bob wants to know how many minimum number of moves he needs to come out(i.e. he reaches the same gate from where he entered into the field) from the square field. Tell the answer to Bob ASAP.
Luckily, you came to know M=N+1.

-----Input-----
- The first line of the input contains an integer T denoting the number of test cases.
-  Each test case contains a single integer N denoting the sides of the square.

-----Output-----
- For each test case, output a single line containing minimum number of moves Bob required to come out from the field.

-----Constraints-----
- 1 ≤ T ≤ 10000
- 1 ≤ N ≤ 1000000000

-----Example-----
Input:
2
1
2

Output:
2
8

-----Explanation-----
Example case 1.Let four corners of square be (0,0), (0,1), (1,1), (1,0). Let gate be at (0,0). Bob takes 2 steps in one move. Let movement of Bob be as follows (0,0) -> (1,1) -> (0,0). Thus minimum moves needed were 2. 
Example case 2.Let four corners of square be (0,0), (0,2), (2,2), (2,0). Let gate be at (0,0). Bob takes 3 steps in one move. Let movement of Bob be as follows (0,0) -> (2,1) -> (0,2) -> (1,0) -> (2,2) -> (0,1) -> (2,0) -> (1,2) -> (0,0). Thus minimum number of moves needed are 8.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible