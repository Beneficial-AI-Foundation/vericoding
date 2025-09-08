/-
Chef's friend Alex runs a movie theatre. Due to the increasing number of platforms for watching movies online, his business is not running well. As a friend, Alex asked Chef to help him maximise his profits. Since Chef is a busy person, he needs your help to support his friend Alex.  
Alex's theatre has four showtimes: 12 PM, 3 PM, 6 PM and 9 PM. He has four movies which he would like to play ― let's call them A, B, C and D. Each of these movies must be played exactly once and all four must be played at different showtimes. For each showtime, the price of a ticket must be one of the following: Rs 25, Rs 50, Rs 75 or Rs 100. The prices of tickets for different showtimes must also be different.
Through his app, Alex receives various requests from his customers. Each request has the form "I want to watch this movie at this showtime". Let's assume that the number of people who come to watch a movie at a given showtime is the same as the number of requests for that movie at that showtime.
It is not necessary to accommodate everyone's requests ― Alex just wants to earn the maximum amount of money. There is no restriction on the capacity of the theatre. However, for each movie that is not watched by anyone, Alex would suffer a loss of Rs 100 (deducted from the profit).
You are given $N$ requests Alex received during one day. Find the maximum amount of money he can earn on that day by choosing when to play which movies and with which prices. 

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- $N$ lines follow. Each of these lines contains a character $m$, followed by a space and an integer $t$, describing a request to see the movie $m$ at the showtime $t$.

-----Output-----
For each test case, print a single line containing one integer ― the maximum profit Alex can earn (possibly negative).
Finally, print a line containing one integer ― the total profit over all test cases, i.e. over $T$ days.

-----Constraints-----
- $1 \le T \le 150$
- $0 \le N \le 100$
- $m$ is 'A', 'B', 'C' or 'D'
- $t$ is $12$, $3$, $6$ or $9$

-----Subtasks-----
Subtask #1 (30 points): it is possible to fulfill all requests
Subtask #2 (70 points): original constraints

-----Example Input-----
5
12
A 3
B 12
C 6
A 9
B 12
C 12
D 3
B 9
D 3
B 12
B 9
C 6
7
A 9
A 9
B 6
C 3
D 12
A 9
B 6
2
A 9
B 6
1
D 12
0 

-----Example Output-----
575
525
-25 
-200 
-400
475

-----Explanation-----
Example case 1: The following table shows the number of people that want to watch the movies at the given showtimes:  12  3  6  9   A   0  1  0 1  B   3  0  0  2   C   1  0  2  0   D   0  2  0  0 
The maximum number of requests was sent for movie B at 12 PM. Therefore, we play this movie at this time and the tickets cost Rs 100. Next, we play movie D at 3 PM with ticket price Rs 75 and movie C at 6 PM with ticket price Rs 50. Finally, we have a slot for 9 PM and the only movie we can play at that time now is movie A, with ticket price Rs 25. The total profit is $3 \cdot 100 + 2 \cdot 75 + 2 \cdot 50 + 1 \cdot 25 = 300 + 150 + 100 + 25 = 575$. Since each movie was watched by at least one person, there is no additional loss.
Example case 2: Just like above, we show the requests in a table:  12  3  6  9   A   0  0  0 3  B   0  0  2  0   C   0  1  0  0   D   1  0  0  0 
The optimal solution is to play movie A at 9 PM, movie B at 6 PM, movie C at 3 PM and movie D at 12 PM, with decreasing ticket prices in this order. The profit is $3 \cdot 100 + 2 \cdot 75 + 1 \cdot 50 + 1 \cdot 25 = 300+150+50+25 = 525$.
Example case 3: Again, we show the requests in a table:  12  3  6  9   A   0  0  0 1  B   0  0  1  0   C   0  0  0  0   D   0  0  0  0 
The optimal solution is to play movie A at 9 PM with ticket price Rs 100, movie B at 6 PM with ticket price Rs 75 and the remaining two movies in any order at 12 PM and 3 PM ― either way, there will be nobody watching them. We earn $1 \cdot 100 + 1 \cdot 75 = 175$, but we have to deduct Rs 200, so the resulting profit is $175 - 200 = -25$.
Example case 4: The optimal solution is to play movie D at 12 PM; the other three movies go unattended. We have to deduct Rs 300, so the profit is $1 \cdot 100 - 300 = -200$.
Example case 5: Since there are no requests for any movie at any time, all movies go unattended and Alex just suffers a loss of Rs 400.
The total profit for all 5 days is $575+525-25-200-400 = 475$.
-/

-- <vc-helpers>
-- </vc-helpers>

def maximize_profit (n : Nat) (requests : List Request) : Int := sorry

theorem profit_is_bounded_above (n : Nat) (requests : List Request) :
  maximize_profit n requests ≤ n * 100 - 100 := sorry

theorem profit_has_lower_bound (n : Nat) (requests : List Request) :
  maximize_profit n requests ≥ -400 := sorry 

theorem empty_requests_profit (requests : List Request) :
  requests = [] → maximize_profit 0 requests = -400 := sorry

theorem single_request_above_min (r : Request) :
  maximize_profit 1 [r] > -400 := sorry 

theorem same_movie_diff_times_above_min (m : Char) :
  let reqs := [⟨m, "3"⟩, ⟨m, "6"⟩, ⟨m, "9"⟩, ⟨m, "12"⟩]
  maximize_profit 4 reqs > -400 := sorry

theorem diff_movies_same_time_above_min (t : String) :
  let reqs := [⟨'A', t⟩, ⟨'B', t⟩, ⟨'C', t⟩, ⟨'D', t⟩] 
  maximize_profit 4 reqs > -400 := sorry

/-
info: 575
-/
-- #guard_msgs in
-- #eval maximize_profit 12 [("A", "3"), ("B", "12"), ("C", "6"), ("A", "9"), ("B", "12"), ("C", "12"), ("D", "3"), ("B", "9"), ("D", "3"), ("B", "12"), ("B", "9"), ("C", "6")]

/-
info: 525
-/
-- #guard_msgs in
-- #eval maximize_profit 7 [("A", "9"), ("A", "9"), ("B", "6"), ("C", "3"), ("D", "12"), ("A", "9"), ("B", "6")]

/-
info: -400
-/
-- #guard_msgs in
-- #eval maximize_profit 0 []

-- Apps difficulty: interview
-- Assurance level: unguarded