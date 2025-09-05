Chef is the event manager of his college. He has been assigned the task to manage the upcoming tech fest. There are $K$ rooms where the event can take place, and at a particular time only one event can be organized in a room for a particular time interval.
Each event coordinator has their strictly preferred room $P_i$, and if the room is already occupied he simply cancels that event.Chef wants to maximize the total number of events,and so he allows or disallows certain events in order to achieve the task . Chef is busy handling his events so the chef needs your help .
Given a list of $N$ events with their start time $S_i$,end time $E_i$ and preferred room $P_i$,you need to calculate the maximum number of events that can take place.
Note that the $i$th event wants to occupy the $p_i$ room from [$s_i$, $f_i$) .

-----Input:-----
The first line contains an integer $T$ denoting the number of test cases . Each of the next $T$ lines contains two integers $N$ and $K$ , the number of events and the number of rooms respectively . Each of the next $N$ lines contains three integers $s_i$ ,$e_i$ and $p_i$,the start time ,end time and the preferred room of ith event.

-----Output:-----
Print the maximum number of events that can take place.

-----Constraints-----
- $1 \leq T \leq 100$
- $1 \leq N \leq 10^3$
- $1 \leq  K \leq 10^5$
- $1 \leq  Si <  Ei \leq 10^9$
- $1 \leq Pi \leq K$

-----Sample Input:-----
1

4 2
1 10 1
10 20 2
15 50 2
20 30 2

-----Sample Output:-----
3

-----EXPLANATION:-----
Chef can allow events 1st ,2nd and 4th,to get the maximum 3.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded