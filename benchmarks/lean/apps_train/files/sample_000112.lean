You play a computer game. In this game, you lead a party of $m$ heroes, and you have to clear a dungeon with $n$ monsters. Each monster is characterized by its power $a_i$. Each hero is characterized by his power $p_i$ and endurance $s_i$.

The heroes clear the dungeon day by day. In the beginning of each day, you choose a hero (exactly one) who is going to enter the dungeon this day.

When the hero enters the dungeon, he is challenged by the first monster which was not defeated during the previous days (so, if the heroes have already defeated $k$ monsters, the hero fights with the monster $k + 1$). When the hero fights the monster, there are two possible outcomes:

  if the monster's power is strictly greater than the hero's power, the hero retreats from the dungeon. The current day ends;  otherwise, the monster is defeated. 

After defeating a monster, the hero either continues fighting with the next monster or leaves the dungeon. He leaves the dungeon either if he has already defeated the number of monsters equal to his endurance during this day (so, the $i$-th hero cannot defeat more than $s_i$ monsters during each day), or if all monsters are defeated — otherwise, he fights with the next monster. When the hero leaves the dungeon, the current day ends.

Your goal is to defeat the last monster. What is the minimum number of days that you need to achieve your goal? Each day you have to use exactly one hero; it is possible that some heroes don't fight the monsters at all. Each hero can be used arbitrary number of times.

-----Input-----

The first line contains one integer $t$ ($1 \le t \le 10^5$) — the number of test cases. Then the test cases follow.

The first line of each test case contains one integer $n$ ($1 \le n \le 2 \cdot 10^5$) — the number of monsters in the dungeon.

The second line contains $n$ integers $a_1$, $a_2$, ..., $a_n$ ($1 \le a_i \le 10^9$), where $a_i$ is the power of the $i$-th monster.

The third line contains one integer $m$ ($1 \le m \le 2 \cdot 10^5$) — the number of heroes in your party.

Then $m$ lines follow, each describing a hero. Each line contains two integers $p_i$ and $s_i$ ($1 \le p_i \le 10^9$, $1 \le s_i \le n$) — the power and the endurance of the $i$-th hero.

It is guaranteed that the sum of $n + m$ over all test cases does not exceed $2 \cdot 10^5$.

-----Output-----

For each test case print one integer — the minimum number of days you have to spend to defeat all of the monsters (or $-1$ if it is impossible).

-----Example-----
Input
2
6
2 3 11 14 1 8
2
3 2
100 1
5
3 5 100 2 3
2
30 5
90 1

Output
5
-1

def maxList (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => List.foldl (fun acc y => max acc y) x xs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded