/-
Bitland declared war on Chefland and sent an army to fight them, but Chefland defended efficiently and Bitland's army has been reduced to N$N$ soldiers. They have no chance of winning the war and do not want to surrender, so they are planning to commit group suicide. Josh, the leader of Bitland's remaining soldiers, has different plans — he wants to survive and somehow escape.
The soldiers are numbered 1$1$ through N$N$; Josh is soldier N$N$. The soldiers are going to stand in a circle in the order 1,2,…,P−1,N,P,P+1,…,N−1$1, 2, \ldots, P-1, N, P, P+1, \ldots, N-1$. Formally, they are standing in the circle in such a way that if Josh's position is P$P$ (1≤P≤N$1 \le P \le N$), then for each i$i$ (1≤i≤N−2$1 \le i \le N-2$, i≠P−1$i \neq P-1$), soldier i+1$i+1$ is directly to the right of soldier i$i$, soldier P$P$ (if P≤N−1$P \le N-1$) or 1$1$ (if P=N$P = N$) is directly to the right of Josh and Josh is directly to the right of soldier P−1$P-1$ (if P≥2$P \ge 2$) or soldier N−1$N-1$ (if P=1$P = 1$); if 2≤P≤N−2$2 \le P \le N-2$, soldier 1$1$ is also directly to the right of soldier N−1$N-1$. For each i$i$ (1≤i≤N−1$1 \le i \le N-1$), soldier i$i$ has a sword with power Ai$A_i$. Josh plans to take a shield with sufficiently high defense power D$D$.
First, the soldiers start to commit group suicide according to the following rules:
- Initially, soldier 1$1$ is the attacking soldier.
- If the attacking soldier is not Josh, this soldier attacks the soldier that is currently to his right.
- When Josh is attacked with power a$a$, the current defense power of his shield decreases by a$a$, and if it becomes negative, Josh dies. When a different soldier is attacked, he does not try to defend and dies immediately. The power of the attacking soldier's sword does not change.
- Then, the next living soldier to the right of the current attacking soldier becomes the attacking soldier and the process continues until there is only one soldier left.
It is clear that this way, Josh cannot be the last survivor. However, Chefland's general Chef plans to interrupt this process as soon as there are exactly two living soldiers of Bitland left (Josh wants to be one of them) by attacking them with Chefland's full firepower F$F$. Since this attack is unexpected, both attacked soldiers try to defend independently with the weapons they have. Josh survives if the current defense power of his shield is at least F$F$. Any other soldier survives only if the power of his sword is strictly greater than F$F$. Since Chefland does not attack again, if both Josh and another soldier survive, then the other soldier will kill Josh. Therefore, Josh wants to be the only survivor of Chefland's attack.
Your task is to find the minimum possible value of D$D$ such that Josh survives if he chooses his position P$P$ optimally (or determine that he cannot survive) and the lowest position P$P$ such that Josh survives if he takes a shield with this defense power D$D$.

-----Input-----
- The first line of the input contains a single integer T$T$ denoting the number of test cases. The description of T$T$ test cases follows.
- The first line of each test case contains a single integer N$N$.
- The second line contains N−1$N-1$ space-separated integers A1,A2,…,AN−1$A_1, A_2, \ldots, A_{N-1}$.
- The third line contains a single integer F$F$.

-----Output-----
For each test case, first, print a line containing the string "possible" if Josh can survive or "impossible" if he cannot (without quotes). Then, if he can survive, print a second line containing two space-separated integers P$P$ and D$D$.

-----Constraints-----
- 1≤T≤1,000$1 \le T \le 1,000$
- 2≤N≤1,000,000$2 \le N \le 1,000,000$
- 1≤Ai≤10,000$1 \le A_i \le 10,000$ for each valid i$i$
- 1≤F≤10,000$1 \le F \le 10,000$
- the sum of N$N$ over all test cases does not exceed 1,000,005$1,000,005$

-----Subtasks-----
Subtask #1 (30 points):
- 1≤T≤10$1 \le T \le 10$
- 2≤N≤100$2 \le N \le 100$
- 1≤Ai≤100$1 \le A_i \le 100$ for each valid i$i$
- 1≤F≤100$1 \le F \le 100$
Subtask #2 (70 points): original constraints

-----Example Input-----
2
5
12 34 45 5
10
5
10 15 43 20
5

-----Example Output-----
possible
4 100
impossible

-----Explanation-----
Example case 1: When Josh is at the position P=4$P = 4$, the soldiers' initial powers in clockwise order around the circle, starting with soldier 1$1$, are [12,34,45,D,5]$[12, 34, 45, D, 5]$ (D$D$ denotes Josh). Then, the following happens:
- The soldier with power 12$12$ attacks the soldier with power 34$34$ and kills him.
- The soldier with power 45$45$ attacks Josh, who defends. The living soldiers' powers are now [12,45,D−45,5]$[12, 45, D-45, 5]$ and Josh is the attacking soldier.
- Josh does not attack, so the soldier to his right (with power 5$5$) becomes the attacking soldier. He attacks the soldier with power 12$12$ and kills him.
- The soldier with power 45$45$ attacks Josh again and Josh defends again.
- The soldier with power 5$5$ attacks the soldier with power 45$45$ and kills him.
- Now, two soldiers are left: Josh (with a shield with defense power D−90$D-90$) and the soldier with a sword with power 5$5$. Each of them is attacked with firepower F=10$F=10$, so the power of Josh's shield drops to D−100$D-100$ and the other soldier dies.
If Josh survives, his shield's initial power D$D$ should be at least 45+45+10=100$45+45+10 = 100$. For all other positions P$P$, Josh cannot survive.
Example case 2: Regardless of how large D$D$ is and which position Josh chooses, after Chefland's attack, a soldier of Bitland other than Josh will always survive. This soldier will then attack Josh until his shield breaks and he dies.
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_bitland_survival (N : Nat) (soldiers : List Nat) (F : Nat) : 
  (String × Option Nat × Option Nat) := sorry

theorem bitland_survival_valid_solution {N : Nat} {soldiers : List Nat} {F : Nat}
  (h1 : N ≥ 2)
  (h2 : soldiers.length = N - 1)
  (h3 : ∀ s ∈ soldiers, s ≥ 1 ∧ s ≤ 100) :
  let (result, pos, shield) := solve_bitland_survival N soldiers F
  (result = "possible" → 
    (∃ p s, pos = some p ∧ shield = some s ∧ 
            p ≥ 1 ∧ p ≤ N-1 ∧ s ≥ F)) ∧
  (result = "impossible" →
    pos = none ∧ shield = none) := sorry

theorem impossible_case {soldiers : List Nat} {F : Nat}
  (h1 : F ≥ 1 ∧ F ≤ 50)
  (h2 : soldiers.length ≥ 1)
  (h3 : soldiers.length ≤ 10)
  (h4 : ∀ s ∈ soldiers, s > F) :
  let N := soldiers.length + 1
  let (result, pos, shield) := solve_bitland_survival N soldiers F
  result = "impossible" ∧ pos = none ∧ shield = none := sorry

theorem single_soldier_case {F : Nat}
  (h1 : F ≥ 1 ∧ F ≤ 50) :
  let (result, pos, shield) := solve_bitland_survival 2 [F-1] F
  result = "possible" ∧ pos = some 1 ∧ shield = some F := sorry

-- Apps difficulty: interview
-- Assurance level: guarded