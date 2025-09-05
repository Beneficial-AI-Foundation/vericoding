A key feature of the Siruseri railway network is that it has exactly one route between any pair of stations.
The government has chosen three contractors to run the canteens at the stations on the railway network. To ensure that there are no disputes between the contractors it has been decided that if two stations, say $A$ and $B$, are assigned to a particular contractor then all the stations that lie on the route from $A$ to $B$ will also be awarded to the same contractor.
The government would like the assignment of stations to the contractors to be as equitable as possible. The government has data on the number of passengers who pass through each station each year. They would like to assign stations so that the maximum number of passengers passing through any contractor's collection of stations is minimized.
For instance, suppose the railway network is as follows, where the volume of passenger traffic is indicated by the side of each station.

One possible assignment would to award stations $1$ and $3$ to one contractor (there by giving him a traffic of $35$ passengers), station $2$ to the second contractor (traffic of $20$) and stations $4, 5$ and $6$ to the third contractor (traffic of $100$). In this assignment, the maximum traffic for any one contractor is 100. On the other hand if we assigned stations $1, 2$ and $3$ to one contractor, station $4$ and $6$ to the second contractor and station $5$ to the third contractor the maximum traffic for any one contractor is $70$. You can check that you cannot do better. (The assignment $1$, $2$ and $3$ to one contractor, $4$ to the second contractor, and $5$ and $6$ to the third contractor has a lower value for the maximum traffic ($55$) but it is not a valid assignment as the route from $5$ to $6$ passes through $4$.)

-----Input:-----
The first line of the input contains one integer $N$ indicating the number of railways stations in the network. The stations are numbered $1,2,..., N$. This is followed by $N$ lines of input, lines $2,3,...,N+1$, indicating the volume of traffic at each station. The volume of traffic at station $i$, $1 \leq i \leq N$, is given by a single integer in line $i+1$. The next $N-1$ lines of input, lines $N+2, N+3, ..., 2 \cdot N$, describe the railway network. Each of these lines contains two integers, denoting a pair of stations that are neighbours.

-----Output:-----
The output should be a single integer, corresponding to the minimum possible value of the maximum traffic of any contractor among all valid assignment of the stations to the three contractors.

-----Constraints:-----
- $1 \leq N \leq 3000$.

-----Sample Input-----
6
10
20
25
40
30
30
4 5
1 3
3 4
2 3
6 4

-----Sample Output-----
70

def List.sum (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: xs => x + xs.sum

def find_min_max_traffic (n: Nat) (traffic: List Nat) (edges: List (Nat × Nat)) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
