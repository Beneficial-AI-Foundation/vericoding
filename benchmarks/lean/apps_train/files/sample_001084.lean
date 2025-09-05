Chef is stuck on the minute hand of a giant clock. To escape from this clock he needs to get onto the hour hand which has an exit door. 
Since the minute hand and and hour hand are not connected at any point, chef will surely need to make a jump. Since he wants minimum risks, he chooses to jump on the hour hand so that the angle he has to cover is minimum possible.
You will be given a clock time in $UTC$ format denoting time of chef's jump and you have to compute the minimum angle that chef needs to cover while completing the jump.
For some reason chef times his jump only when the number of minutes is a multiple of 5.

-----Input:-----
The first line of the input contains a single integer $T$ denoting the number of test cases. The description of  $T$ test cases follows.
The first line of each test case contains a string denoting time in UTC format (e.g. 10:20 i.e. 10 hours and 20 minutes)

-----Output-----
For each test case, print a single line denoting the smallest angle of jump.

-----Constraints-----
- $1 \leq T \leq 10^3$
- $0 \leq hours \leq 23$
- $0 \leq minutes \leq 59$

-----Example Input-----
3
14:20
02:10
09:30

-----Example Output-----
50 degree 
5 degree  
105 degree

-----Explanation-----
- In the second case, once the hour hand reaches 2 it starts moving towards 3 with the passing of every minute, hence when the minute hand points 10 minutes, the hour hand has already covered some angle towards 3. 
In this scenario the two angles made by hour and minute hand are 355 and 5 degrees. Since chef will jump on the side with minimum angle, he chooses the one with 5-degree angle.

def find_min_angle (t : Time) : String := sorry

def string_to_float (s : String) : Float := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
