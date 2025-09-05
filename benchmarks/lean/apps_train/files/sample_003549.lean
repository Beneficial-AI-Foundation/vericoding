# Task

In the city, a bus named Fibonacci runs on the road every day.

There are `n` stations on the route. The Bus runs from station1 to stationn.

At the departure station(station1), `k` passengers get on the bus. 

At the second station(station2), a certain number of passengers get on and the same number get off. There are still `k` passengers on the bus.

From station3 to stationn-1, the number of boarding and alighting passengers follows the following rule:

- At stationi, the number of people getting on is the sum of the number of people getting on at the two previous stations(stationi-1 and stationi-2)
- The number of people getting off is equal to the number of people getting on at the previous station(stationi-1).

At stationn, all the passengers get off the bus. 

Now, The numbers we know are: `k` passengers get on the bus at station1, `n` stations in total, `m` passengers get off the bus at stationn.

We want to know: How many passengers on the bus when the bus runs out stationx.

# Input

- `k`: The number of passengers get on the bus at station1.
  - `1 <= k <= 100`

- `n`: The total number of stations(1-based).
  - `6 <= n <= 30`

- `m`: The number of passengers get off the bus at stationn.
  - `1 <= m <= 10^10`

- `x`: Stationx(1-based). The station we need to calculate.
  - `3 <= m <= n-1`

- All inputs are valid integers.

# Output

An integer. The number of passengers on the bus when the bus runs out stationx.

def sim (k n : Nat) (p : Float) : Float :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
