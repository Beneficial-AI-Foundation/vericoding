After failing to clear his school mathematics examination, infinitepro decided to prepare very hard for his upcoming re-exam, starting with the topic he is weakest at ― computational geometry.
Being an artist, infinitepro has C$C$ pencils (numbered 1$1$ through C$C$); each of them draws with one of C$C$ distinct colours. He draws N$N$ lines (numbered 1$1$ through N$N$) in a 2D Cartesian coordinate system; for each valid i$i$, the i$i$-th line is drawn with the ci$c_i$-th pencil and it is described by the equation y=ai⋅x+bi$y = a_i \cdot x + b_i$.
Now, infinitepro calls a triangle truly-geometric if each of its sides is part of some line he drew and all three sides have the same colour. He wants to count these triangles, but there are too many of them! After a lot of consideration, he decided to erase a subset of the N$N$ lines he drew. He wants to do it with his eraser, which has length K$K$.
Whenever erasing a line with a colour i$i$, the length of the eraser decreases by Vi$V_i$. In other words, when the eraser has length k$k$ and we use it to erase a line with a colour i$i$, the length of the eraser decreases to k−Vi$k-V_i$; if k<Vi$k < V_i$, it is impossible to erase such a line.
Since infinitepro has to study for the re-exam, he wants to minimise the number of truly-geometric triangles. Can you help him find the minimum possible number of truly-geometric triangles which can be obtained by erasing a subset of the N$N$ lines in an optimal way? He promised a grand treat for you if he passes the examination!

-----Input-----
- The first line of the input contains a single integer T$T$ denoting the number of test cases. The description of T$T$ test cases follows.
- The first line of the input contains three space-separated integers N$N$, C$C$ and K$K$.
- N$N$ lines follow. For each i$i$ (1≤i≤N$1 \le i \le N$), the i$i$-th of these lines contains three space-separated integers ai$a_i$, bi$b_i$ and ci$c_i$.
- The last line contains C$C$ space-separated integers V1,V2,…,VC$V_1, V_2, \ldots, V_C$.

-----Output-----
For each test case, print a single line containing one integer ― the smallest possible number of truly-geometric triangles after erasing lines.

-----Constraints-----
- 1≤T≤10$1 \le T \le 10$
- 1≤C≤N≤3,000$1 \le C \le N \le 3,000$
- 0≤K≤3,000$0 \le K \le 3,000$
- 0≤ai,bi≤109$0 \le a_i, b_i \le 10^9$ for each valid i$i$
- 1≤ci≤C$1 \le c_i \le C$ for each valid i$i$
- 0≤Vi≤K$0 \le V_i \le K$ for each valid i$i$
- no two lines coincide, regardless of their colours
- no three lines are concurrent

-----Subtasks-----
Subtask #1 (10 points):
- N≤10$N \le 10$
- K≤100$K \le 100$
Subtask 2 (15 points):
- V1=V2=…=VC$V_1 = V_2 = \ldots = V_C$
- no two lines are parallel
Subtask #3 (25 points): no two lines are parallel
Subtask #4 (50 points): original constraints

-----Example Input-----
2
7 2 13
1 10 1
1 14 2
6 4 1
2 2 1
0 12 2
2 11 2
0 6 1
8 10
6 1 20
1 5 1
2 11 1
4 0 1
6 8 1
0 11 1
3 3 1
9

-----Example Output-----
2
4

-----Explanation-----
Example case 1: We can remove exactly one line. Initially, we have 5$5$ truly geometric triangles (see the image below; red is colour 1$1$ and green is colour 2$2$).
- Removing any line with colour 2$2$ brings the total number of truly-geometric triangles down to 4+0=4$4+0=4$.
- Removing any line with colour 1$1$ brings the total number of truly-geometric triangles down to 1+1=2$1+1=2$.
Thus, the smallest number of truly-geometric triangles we can obtain is 2$2$.

Example case 2: We can remove at most 2$2$ lines and removing any 2$2$ lines gives us a total of 4$4$ truly-geometric triangles.

def nc3 (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
