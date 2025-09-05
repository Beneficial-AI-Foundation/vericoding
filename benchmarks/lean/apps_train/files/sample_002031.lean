Polycarp starts his own business. Tomorrow will be the first working day of his car repair shop. For now the car repair shop is very small and only one car can be repaired at a given time.

Polycarp is good at marketing, so he has already collected n requests from clients. The requests are numbered from 1 to n in order they came.

The i-th request is characterized by two values: s_{i} — the day when a client wants to start the repair of his car, d_{i} — duration (in days) to repair the car. The days are enumerated from 1, the first day is tomorrow, the second day is the day after tomorrow and so on.

Polycarp is making schedule by processing requests in the order from the first to the n-th request. He schedules the i-th request as follows:  If the car repair shop is idle for d_{i} days starting from s_{i} (s_{i}, s_{i} + 1, ..., s_{i} + d_{i} - 1), then these days are used to repair a car of the i-th client.  Otherwise, Polycarp finds the first day x (from 1 and further) that there are d_{i} subsequent days when no repair is scheduled starting from x. In other words he chooses the smallest positive x that all days x, x + 1, ..., x + d_{i} - 1 are not scheduled for repair of any car. So, the car of the i-th client will be repaired in the range [x, x + d_{i} - 1]. It is possible that the day x when repair is scheduled to start will be less than s_{i}. 

Given n requests, you are asked to help Polycarp schedule all of them according to the rules above.

-----Input-----

The first line contains integer n (1 ≤ n ≤ 200) — the number of requests from clients.

The following n lines contain requests, one request per line. The i-th request is given as the pair of integers s_{i}, d_{i} (1 ≤ s_{i} ≤ 10^9, 1 ≤ d_{i} ≤ 5·10^6), where s_{i} is the preferred time to start repairing the i-th car, d_{i} is the number of days to repair the i-th car.

The requests should be processed in the order they are given in the input.

-----Output-----

Print n lines. The i-th line should contain two integers — the start day to repair the i-th car and the finish day to repair the i-th car.

-----Examples-----
Input
3
9 2
7 3
2 4

Output
9 10
1 3
4 7

Input
4
1000000000 1000000
1000000000 1000000
100000000 1000000
1000000000 1000000

Output
1000000000 1000999999
1 1000000
100000000 100999999
1000001 2000000

def scheduleRepairs (requests : List (Nat × Nat)) : List (Nat × Nat) := sorry

def isNonOverlapping (intervals : List (Nat × Nat)) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
