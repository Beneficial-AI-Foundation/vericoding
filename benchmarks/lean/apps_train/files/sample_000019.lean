The only difference between easy and hard versions is constraints.

The BerTV channel every day broadcasts one episode of one of the $k$ TV shows. You know the schedule for the next $n$ days: a sequence of integers $a_1, a_2, \dots, a_n$ ($1 \le a_i \le k$), where $a_i$ is the show, the episode of which will be shown in $i$-th day.

The subscription to the show is bought for the entire show (i.e. for all its episodes), for each show the subscription is bought separately.

How many minimum subscriptions do you need to buy in order to have the opportunity to watch episodes of purchased shows $d$ ($1 \le d \le n$) days in a row? In other words, you want to buy the minimum number of TV shows so that there is some segment of $d$ consecutive days in which all episodes belong to the purchased shows.

-----Input-----

The first line contains an integer $t$ ($1 \le t \le 10000$) — the number of test cases in the input. Then $t$ test case descriptions follow.

The first line of each test case contains three integers $n, k$ and $d$ ($1 \le n \le 2\cdot10^5$, $1 \le k \le 10^6$, $1 \le d \le n$). The second line contains $n$ integers $a_1, a_2, \dots, a_n$ ($1 \le a_i \le k$), where $a_i$ is the show that is broadcasted on the $i$-th day.

It is guaranteed that the sum of the values ​​of $n$ for all test cases in the input does not exceed $2\cdot10^5$.

-----Output-----

Print $t$ integers — the answers to the test cases in the input in the order they follow. The answer to a test case is the minimum number of TV shows for which you need to purchase a subscription so that you can watch episodes of the purchased TV shows on BerTV for $d$ consecutive days. Please note that it is permissible that you will be able to watch more than $d$ days in a row.

-----Example-----
Input
4
5 2 2
1 2 1 2 1
9 3 3
3 3 3 2 2 2 1 1 1
4 10 4
10 8 6 4
16 9 8
3 1 4 1 5 9 2 6 5 3 5 8 9 7 9 3

Output
2
1
4
5

-----Note-----

In the first test case to have an opportunity to watch shows for two consecutive days, you need to buy a subscription on show $1$ and on show $2$. So the answer is two.

In the second test case, you can buy a subscription to any show because for each show you can find a segment of three consecutive days, consisting only of episodes of this show.

In the third test case in the unique segment of four days, you have four different shows, so you need to buy a subscription to all these four shows.

In the fourth test case, you can buy subscriptions to shows $3,5,7,8,9$, and you will be able to watch shows for the last eight days.

def maximum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => List.foldl Nat.max x xs

def listToFinset (l : List Nat) : List Nat :=
  l.eraseDups

def windowsOfSize (l : List Nat) (size : Nat) : List (List Nat) :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
