/-
Back in 2015, Usain Bolt announced that he'll be retiring after the 2017 World Championship. Though his final season did not end gloriously, we all know that he is a true legend and we witnessed his peak during 2008 - 2013. 
Post retirement, Usain Bolt is still leading an adventurous life. He's exploring the unexplored parts of the globe. But sometimes he gets bored, and reads questions asked about him on Quora. One such question he read was, "Who would win a race between Usain Bolt and a tiger if the race is on a straight line track and the tiger is $distancetoBolt$ meters behind Bolt? The finishing point is $finish$ meters away from Bolt's starting position. The tiger starts with an initial speed of $0$ $meter/second$, and will accelerate itself with $tigerAccelaration$ $m/s^2$. Bolt can run with a constant speed of $boltSpeed$ $m/s$ from start to finish. Given these values, find out who will win the race - Bolt or the tiger? "
Note that Bolt will win the race if and only if he touches the finishing line before the tiger touches it. If both of them finish together, the tiger is announced as the winner since Bolt was given an initial advantage. See the figure below for more clarity.

Since Bolt was busy practicing in the tracks during his Physics school classes, he is asking for your help to solve the question. Can you please help him?
He just remembers two formulae from the class, and thinks that they will be useful to you:
$Displacement (S) $ = $ut$ +$ (1/2)at^2$ where $u$ is the initial velocity , #$ $is the acceleration and $t$ is the time taken.
$Velocity$ = $Displacement /Time$

-----Input:-----
- The first line will contain $T$, the number of testcases. Then the description of each test case follow. 
- Each test case contains 4 integers $finish, distancetoBolt, tigerAccelaration, boltSpeed$. 

-----Output:-----
For each testcase, output in a single line, the word "Bolt" or "Tiger" without quotes, depending on whether Bolt wins or the tiger wins.

-----Constraints-----
- $1 \leq T \leq 100000$
- $1 \leq finish\leq 10^5$
- $1 \leq distancetoBolt\leq 10^5$
- $1 \leq tigerAccelaration\leq 10^5$
- $1 \leq boltSpeed\leq 10^5$

-----Sample Input:-----
2
10 100 10 10
100 10 5 10

-----Sample Output:-----
Bolt
Tiger
-/

-- <vc-helpers>
-- </vc-helpers>

def race_winner (finish : Float) (distance_to_bolt : Float) (tiger_acceleration : Float) (bolt_speed : Float) : String := sorry

theorem race_winner_returns_valid_result (finish : Float) (distance_to_bolt : Float) (tiger_acceleration : Float) (bolt_speed : Float)
    (h1 : finish > 0) 
    (h2 : distance_to_bolt > 0)
    (h3 : tiger_acceleration > 0)
    (h4 : bolt_speed > 0) :
    (race_winner finish distance_to_bolt tiger_acceleration bolt_speed = "Bolt" ∨
     race_winner finish distance_to_bolt tiger_acceleration bolt_speed = "Tiger") := sorry

theorem race_winner_correct_winner (finish : Float) (distance_to_bolt : Float) (tiger_acceleration : Float) (bolt_speed : Float)
    (h1 : finish > 0)
    (h2 : distance_to_bolt > 0)
    (h3 : tiger_acceleration > 0) 
    (h4 : bolt_speed > 0) :
    let tiger_time := Float.sqrt (2 * (finish + distance_to_bolt) / tiger_acceleration);
    let bolt_time := finish / bolt_speed;
    (race_winner finish distance_to_bolt tiger_acceleration bolt_speed = "Bolt" → tiger_time > bolt_time) ∧
    (race_winner finish distance_to_bolt tiger_acceleration bolt_speed = "Tiger" → tiger_time ≤ bolt_time) := sorry

theorem infinite_acceleration_tiger_wins (finish : Float) (distance_to_bolt : Float) (bolt_speed : Float)
    (h1 : finish > 0)
    (h2 : distance_to_bolt > 0)
    (h3 : bolt_speed > 0)
    (h4 : tiger_acceleration > 1000000) :
    race_winner finish distance_to_bolt tiger_acceleration bolt_speed = "Tiger" := sorry

/-
info: 'Bolt'
-/
-- #guard_msgs in
-- #eval race_winner 10 100 10 10

/-
info: 'Tiger'
-/
-- #guard_msgs in
-- #eval race_winner 100 10 5 10

/-
info: 'Tiger'
-/
-- #guard_msgs in
-- #eval race_winner 50 50 5 5

-- Apps difficulty: interview
-- Assurance level: unguarded