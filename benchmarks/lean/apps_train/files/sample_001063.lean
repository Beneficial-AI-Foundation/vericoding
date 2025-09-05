Sinchan and his friends loves to eat. They have a 2D rectangular cake which they want to share. Sinchan is very kind and offers his friends to eat the cake first, all friends goes one by one to eat the cake. Each friend will cut cake into two parts. First part of the cake will be largest possible square from the cake, that the friend will eat, and will leave the second part for others, it continues untill cake is over or every friend gets to eat the cake.
Now Sinchan wonder how much cake would he be able to get.

-----Input-----
- First line of input contain T, denoting number of test case.
- First line of each test case contains N, denoting number of friends.
- Second line of test case contain L, B (L x B) denoting dimension of cake.

-----Output-----
- For each test case, if Sinchan gets to eat the cake print (without quotes) "Yes #" where # is area of cake that Sinchan gets. Otherwise print  (without quotes) "No"

-----Constraints-----
- 1 ≤ T, N, L, B ≤ 1000

-----Example-----
Input:
3
2
5 3
4
4 8
1
1 2

Output:
Yes 2
No
Yes 1

-----Explanation-----
Example case 1. First friend divides 5x3 cake in 3x3 and 2x3 since 3x3 is largest possible square, second Friend divides 2x3 cake in 2x2 and 1x2 and eat 2x2 piece. Finaly Sinchan gets to eat and area of cake is 1*2 hence Output is (without quotes) "Yes 2"

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
