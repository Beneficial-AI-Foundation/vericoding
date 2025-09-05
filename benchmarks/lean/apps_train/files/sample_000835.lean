Problem description.
Dominic Toretto has taken his crew to compete in this years' Race Wars, a crew-on-crew tournament in which each member of one crew competes with a member of the other crew in a quarter mile drag race. Each win counts as one point for the winning crew. Draws and loses are awarded zero points. In the end the crew with more points is declared the winner of that round and can advance while the losing crew is knocked out. One member can compete in only one race per round and all crews have the same number of members.
Dom and his crew have a reputation of being the best and naturally everyone expects them to win this year as well.
However, during the tournament he spots a new crew of racers who are participating for the first time in this event. People expect them to be a dark horse so naturally Dom wants to keep an eye on their performance.
Being the experienced racer that he is, Dom has figured out the time in which each racer of the opposing crew completes his quarter mile race.

He also knows his own crew inside out and can estimate with absolute certainty, the time it would take each of his members to complete the race. Dominic is the reigning champion and thus has an advantage that he can select the order of the matches i.e.: he can select which member of his crew will go up against which member of the opposition. Given this data he wants to figure out the number of races he will win should his crew come face to face with their newest rivals.

Unfortunately he is a racer and not a problem solver so he comes to you for help.

Given the time each member of the two crews take to complete the race you have to figure out a way to arrange the matches so that Dominic can win maximum points possible for him.

-----Input-----

The first line of input is the T, the number of test cases.

Each test case starts with a single number N, the number of racers on each crew.

This is followed by two lines, each having N space separated integers containing the time taken by each member of Dominic's crew and the rival crew respectively.

-----Output-----
Output a single integer. The maximum number of points that Dominic can get.

-----Constraints-----
1<=T<=100
1<=N<=100
Time taken by each member will be between 1 and 500

-----Example-----
Input:

1
3
5 4 1
5 4 1

Output:
2

-----Explanation-----
If Dom selects Racer 1 of his team to go against Racer 2 of the other team, Racer 2 of his team against Racer 3 of the other team and Racer 3 of his team against Racer 1 of the other team then he ends up with two wins and a loss which gives him 2 points. ...

def max_race_wins (n : Nat) (my_times : List Nat) (opp_times: List Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded