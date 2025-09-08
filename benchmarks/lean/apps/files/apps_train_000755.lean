/-
Nobody knows, but $N$ frogs live in Chef's garden.
Now they are siting on the X-axis and want to speak to each other. One frog can send a message to another one if the distance between them is less or equal to $K$.
Chef knows all $P$ pairs of frogs, which want to send messages. Help him to define can they or not!
Note : More than $1$ frog can be on the same point on the X-axis.

-----Input-----
- The first line contains three integers $N$, $K$ and $P$.
- The second line contains $N$ space-separated integers $A_1$, $A_2$, …, $A_N$ denoting the x-coordinates of frogs".
- Each of the next $P$ lines contains two integers $A$ and $B$ denoting the numbers of frogs according to the input.

-----Output-----
For each pair print "Yes" without a brackets if frogs can speak and "No" if they cannot.

-----Constraints-----
- $1 \le N, P \le 10^5$
- $0 \le A_i, K \le 10^9$
- $1 \le A, B \le N$

-----Example-----

-----Sample Input:-----
5 3 3
0 3 8 5 12
1 2
1 3
2 5

-----Sample Output:-----
Yes
Yes
No

-----Explanation-----
- 
For pair $(1, 2)$ frog $1$ can directly speak to the frog $2$ as the distance between them is $3 - 0 = 3 \le K$ . 
- 
For pair $(1, 3)$ frog $1$ can send a message to frog $2$, frog $2$ can send it to frog $4$ and it can send it to frog $3$.
- 
For pair $(2, 5)$ frogs can't send a message under current constraints.
-/

-- <vc-helpers>
-- </vc-helpers>

def absolute_value (x : Int) : Int := if x ≥ 0 then x else -x

def can_frogs_communicate (n : Nat) (k : Int) (coords : List Int) (pairs : List (Nat × Nat)) : List String := sorry

theorem can_frogs_communicate_output_format 
  {n : Nat} {k : Int} {coords : List Int} {pairs : List (Nat × Nat)}
  (h1 : n ≥ 2)
  (h2 : coords.length = n)
  (h3 : coords.Nodup)
  (h4 : pairs.length > 0) :
  let result := can_frogs_communicate n k coords pairs
  result.length = pairs.length ∧ 
  ∀ x, x ∈ result → x = "Yes" ∨ x = "No" := sorry

theorem can_frogs_communicate_reflexive
  {n : Nat} {k : Int} {coords : List Int}
  (h1 : n ≥ 2)
  (h2 : coords.length = n)
  (h3 : coords.Nodup) :
  let same_pairs := List.map (fun i => (i+1, i+1)) (List.range n)
  let result := can_frogs_communicate n k coords same_pairs
  ∀ x, x ∈ result → x = "Yes" := sorry

theorem can_frogs_communicate_distance
  {n : Nat} {k : Int} {coords : List Int} {pairs : List (Nat × Nat)}
  (h1 : n ≥ 2)
  (h2 : coords.length = n)
  (h3 : coords.Nodup)
  (h4 : pairs.length > 0) :
  let result := can_frogs_communicate n k coords pairs
  ∀ (i : Nat), i < pairs.length →
    result[i]! = "Yes" →
    ∀ x y, x ∈ coords → y ∈ coords →
      x ≥ min (coords[pairs[i]!.1-1]!) (coords[pairs[i]!.2-1]!) →
      y ≤ max (coords[pairs[i]!.1-1]!) (coords[pairs[i]!.2-1]!) →
      absolute_value (x - y) ≤ k := sorry

theorem can_frogs_communicate_symmetric 
  {n : Nat} {k : Int} {coords : List Int} {pairs : List (Nat × Nat)}
  (h1 : n ≥ 2)
  (h2 : coords.length = n)
  (h3 : coords.Nodup)
  (h4 : pairs.length > 0) :
  let reverse_pairs := pairs.map (fun p => (p.2, p.1))
  can_frogs_communicate n k coords pairs = 
  can_frogs_communicate n k coords reverse_pairs := sorry

-- Apps difficulty: interview
-- Assurance level: guarded