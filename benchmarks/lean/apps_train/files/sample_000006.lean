Arthur owns a ski resort on a mountain. There are $n$ landing spots on the mountain numbered from $1$ to $n$ from the top to the foot of the mountain. The spots are connected with one-directional ski tracks. All tracks go towards the foot of the mountain, so there are no directed cycles formed by the tracks. There are at most two tracks leaving each spot, but many tracks may enter the same spot.

A skier can start skiing from one spot and stop in another spot if there is a sequence of tracks that lead from the starting spot and end in the ending spot. Unfortunately, recently there were many accidents, because the structure of the resort allows a skier to go through dangerous paths, by reaching high speed and endangering himself and the other customers. Here, a path is called dangerous, if it consists of at least two tracks.

Arthur wants to secure his customers by closing some of the spots in a way that there are no dangerous paths in the resort. When a spot is closed, all tracks entering and leaving that spot become unusable. 

Formally, after closing some of the spots, there should not be a path that consists of two or more tracks.

Arthur doesn't want to close too many spots. He will be happy to find any way to close at most $\frac{4}{7}n$ spots so that the remaining part is safe. Help him find any suitable way to do so.

-----Input-----

The first line contains a single positive integer $T$ — the number of test cases. $T$ test case description follows.

The first line of each description contains two integers $n$ and $m$ ($1 \leq n \leq 2 \cdot 10^5$) — the number of landing spots and tracks respectively.

The following $m$ lines describe the tracks. Each of these lines contains two integers $x$ and $y$ ($1 \leq x < y \leq n$) — indices of the starting and finishing spots for the respective track. It is guaranteed that at most two tracks start at each spot. There may be tracks in which starting and finishing spots both coincide.

It is guaranteed that the sum of $n$ over all test cases does not exceed $2 \cdot 10^5$.

-----Output-----

For each test case, print a single integer $k$ ($0 \leq k \leq \frac{4}{7}n$) — the number of spots to be closed. In the next line, print $k$ distinct integers — indices of all spots to be closed, in any order.

If there are several answers, you may output any of them. Note that you don't have to minimize $k$. It can be shown that a suitable answer always exists.

-----Example-----
Input
2
4 6
1 2
1 3
2 3
2 4
3 4
3 4
7 6
1 2
1 3
2 4
2 5
3 6
3 7

Output
2
3 4 
4
4 5 6 7 

-----Note-----

In the first sample case, closing any two spots is suitable.

In the second sample case, closing only the spot $1$ is also suitable.

def valid_track (n : Nat) (track : Nat × Nat) : Prop :=
  let (u, v) := track
  1 ≤ u ∧ u ≤ n ∧ 1 ≤ v ∧ v ≤ n ∧ u ≠ v

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded