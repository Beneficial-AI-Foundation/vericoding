The government has invited bids from contractors to run canteens at all railway stations. Contractors will be allowed to bid for the catering contract at more than one station. However, to avoid monopolistic price-fixing, the government has declared that no contractor may bid for a pair of neighbouring stations.
The railway network has exactly one route between any pair of stations. Each station is directly connected by a railway line to at most $50$ neighbouring stations.
To help contractors plan their bids, the government has provided data on the number of passengers who pass through each station each year. Contractors would like to bid for stations with a higher volume of passenger traffic to increase their turnover.
For instance, suppose the railway network is as follows, where the volume of passenger traffic is indicated by the side of each station.

In this network, the best option for the contractor is to bid for stations $1, 2, 5$ and $6$, for a total passenger volume of $90$.
Your task is to choose a set of stations that the contractor should bid for so that the total volume of traffic across all the stations in the bid is maximized.

-----Input:-----
The first line of the input contains one integer $N$ indicating the number of railways stations in the network. The stations are numbered $1,2,...,N$. This is followed by $N$ lines of input, lines $2, 3,..., N+1$, indicating the volume of traffic at each station. The volume of traffic at station $i, 1 \leq i \leq N$, is given by a single integer in line $i+1$. The next $N-1$ lines of input, lines $N+2, N+3, ..., 2N$, describe the railway network. Each of these lines contains two integers, denoting a pair of stations that are neighbours.

-----Output:-----
The output should be a single integer, corresponding to the total volume of traffic across the set of stations in the optimal bid made by the contractor.

-----Constraints:-----
- $1 \leq N \leq 100000$. 
- Each railway station has at most $50$ neighbours.

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
90

def sum (list : List Nat) : Nat :=
  match list with
  | [] => 0
  | x::xs => x + sum xs

def maximum (list : List Nat) : Nat :=
  match list with
  | [] => 0
  | [x] => x
  | x::xs => Nat.max x (maximum xs)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
