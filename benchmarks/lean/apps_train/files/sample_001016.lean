Chef bought a huge (effectively infinite) planar island and built $N$ restaurants (numbered $1$ through $N$) on it. For each valid $i$, the Cartesian coordinates of restaurant $i$ are $(X_i, Y_i)$.
Now, Chef wants to build $N-1$ straight narrow roads (line segments) on the island. The roads may have arbitrary lengths; restaurants do not have to lie on the roads. The slope of each road must be $1$ or $-1$, i.e. for any two points $(x_1, y_1)$ and $(x_2, y_2)$ on the same road, $|x_1-x_2| = |y_1-y_2|$ must hold.
Let's denote the minimum distance Chef has to walk from restaurant $i$ to reach a road by $D_i$. Then, let's denote $a = \mathrm{max}\,(D_1, D_2, \ldots, D_N)$; Chef wants this distance to be minimum possible.
Chef is a busy person, so he decided to give you the job of building the roads. You should find a way to build them that minimises $a$ and compute $a \cdot \sqrt{2}$.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- $N$ lines follow. For each valid $i$, the $i$-th of these lines contains two space-separated integers $X_i$ and $Y_i$.

-----Output-----
For each test case, print a single line containing one real number — the minimum distance $a$ multiplied by $\sqrt{2}$. Your answer will be considered correct if its absolute or relative error does not exceed $10^{-6}$.

-----Constraints-----
- $1 \le T \le 100$
- $2 \le N \le 10^4$
- $|X_i|, |Y_i| \le 10^9$ for each valid $i$

-----Subtasks-----
Subtask #1 (10 points):
- $1 \le T \le 10$
- $2 \le N \le 5$
- $|X_i|, |Y_i| \le 10$ for each valid $i$
- $a \cdot \sqrt{2}$ is an integer
Subtask #2 (90 points): original constraints

-----Example Input-----
2
3
0 0
0 1
0 -1
3
0 1
1 0
-1 0

-----Example Output-----
0.5
0

-----Explanation-----
Example case 1: We should build roads described by equations $y-x+0.5 = 0$ and $y-x-0.5 = 0$.
Example case 2: We should build roads described by equations $y-x-1 = 0$ and $y+x-1 = 0$.

def manhattan_distance (p1 p2 : Point) : Nat :=
  let dx := (p1.x - p2.x).toNat
  let dy := (p1.y - p2.y).toNat
  dx + dy

def euclidean_distance (p1 p2 : Point) : Float :=
  let dx := (p1.x - p2.x).toNat.toFloat
  let dy := (p1.y - p2.y).toNat.toFloat
  Float.sqrt (dx * dx + dy * dy)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
