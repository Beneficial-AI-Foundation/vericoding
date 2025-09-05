A festival will be held in a town's main street. There are n sections in the main street. The sections are numbered 1 through n from left to right. The distance between each adjacent sections is 1.

In the festival m fireworks will be launched. The i-th (1 ≤ i ≤ m) launching is on time t_{i} at section a_{i}. If you are at section x (1 ≤ x ≤ n) at the time of i-th launching, you'll gain happiness value b_{i} - |a_{i} - x| (note that the happiness value might be a negative value).

You can move up to d length units in a unit time interval, but it's prohibited to go out of the main street. Also you can be in an arbitrary section at initial time moment (time equals to 1), and want to maximize the sum of happiness that can be gained from watching fireworks. Find the maximum total happiness.

Note that two or more fireworks can be launched at the same time.

-----Input-----

The first line contains three integers n, m, d (1 ≤ n ≤ 150000; 1 ≤ m ≤ 300; 1 ≤ d ≤ n).

Each of the next m lines contains integers a_{i}, b_{i}, t_{i} (1 ≤ a_{i} ≤ n; 1 ≤ b_{i} ≤ 10^9; 1 ≤ t_{i} ≤ 10^9). The i-th line contains description of the i-th launching.

It is guaranteed that the condition t_{i} ≤ t_{i} + 1 (1 ≤ i < m) will be satisfied.

-----Output-----

Print a single integer — the maximum sum of happiness that you can gain from watching all the fireworks.

Please, do not write the %lld specifier to read or write 64-bit integers in C++. It is preferred to use the cin, cout streams or the %I64d specifier.

-----Examples-----
Input
50 3 1
49 1 1
26 1 4
6 1 10

Output
-31

Input
10 2 1
1 1000 4
9 1000 4

Output
1992

def solve_fireworks (n m d : Nat) (fireworks : List (Nat × Nat × Nat)) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
