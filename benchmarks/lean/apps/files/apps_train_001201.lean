/-
A Train started its journey at x=-infinity is travelling on the x-Coordinate Axis. Given n passengers and the coordinates $b_i$ and $d_i$ for each of the $ith$ passenger at which they board and leave from the train respectively. Due to current COVID-19 crisis, the train is monitored at each mile/coordinate. The infection degree of the train at each mile is equal to the total passengers present in the train at that mile/coordinate. The train stops its journey if no more passengers are there to board the train. The term infection severity of the journey is defined as the sum of infection degrees noted at each mile. Find the Infection severity of the journey. Note: A passenger is considered for calculation of infection degree at both boarding and leaving stations.

Since the answer can be very large, print it modulo $(10^9)+7$.

-----Input:-----
- First line will contain $N$, number of passengers. Then the $N$ lines follow. 
- $i$th line contains two integers $b_i, d_i$ , the boarding and departure mile of $i$th passenger.

-----Output:-----
Print a single value, the Infection Severity of the journey modulo $(10^9)+7$.

-----Constraints-----
- $0 \leq N \leq 100000$
- $-500000 \leq b_i \leq 500000$
- $-500000 \leq d_i \leq 500000$

-----Sample Input:-----
3

0 2

1 3

-1 4  

-----Sample Output:-----
12    

-----EXPLANATION:-----
Infection degree at :

-1 is 1

0 is 2

1 is 3

2 is 3

3 is 2

4 is 1

Calculation started at mile -1 and ended at mile 4. Infection Severity = 1+2+3+3+2+1 =12
-/

-- <vc-helpers>
-- </vc-helpers>

def calculate_infection_severity (passengers : List String) : Nat :=
  sorry

theorem severity_matches_manual_calc
    (coords : List (Int × Int)) :
    let passengers := coords.map (fun (x : Int × Int) => s!"{x.1} {x.2}")
    let manual_calc := coords.foldl (fun acc x => (acc + (x.2 - x.1).natAbs + 1) % (10^9 + 7)) 0
    calculate_infection_severity passengers = manual_calc :=
sorry

theorem zero_distance_severity
    (xs : List Int) :
    let passengers := xs.map (fun x => s!"{x} {x}")
    calculate_infection_severity passengers = xs.length :=
sorry

/-
info: 12
-/
-- #guard_msgs in
-- #eval calculate_infection_severity ["0 2", "1 3", "-1 4"]

/-
info: 6
-/
-- #guard_msgs in
-- #eval calculate_infection_severity ["0 5"]

/-
info: 2
-/
-- #guard_msgs in
-- #eval calculate_infection_severity ["1 1", "2 2"]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible