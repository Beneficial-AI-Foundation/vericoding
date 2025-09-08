/-
Chef will not be able to attend the birthday of his best friend Rock. He promised Rock that this will not be the case on his half birthday. To keep his promise Chef must know Rock’s next half birthday accurately. Being busy, he is assigning this work to you.
Half birthday is the day that occurs exactly between two subsequent birthdays. 
You will be provided with Rock’s birthdate and birth month, you will have to figure out his half birthday.
$Note$: Consider every year to be a leap year and all months are displayed in lowercase English characters.

-----Input:-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. 
- The description of each of the $T$ test cases contains an integer $d$ followed by a string, denoting month $m$.
- Here $d$ denotes day of a month and $m$ denotes the month of a year respectively.

-----Output:-----
For each test case print an integer $d1$ followed by a string, denoting month $m1$, which overall denotes date and month of Rock’s half birthday.

-----Constraints:-----
- $1 \leq T \leq 10^5$
- $1 \leq d , d1 \leq 31$
- $january \leq m , m1 \leq december$

-----Sample Input:-----
3
15 january
31 august
10 october

-----Sample Output:-----
16 july
1 march
10 april
-/

def daysInMonth (m : Month) : Nat :=
  match m with
  | Month.february => 29
  | Month.april | Month.june | Month.september | Month.november => 30
  | _ => 31

def find_half_birthday (day : Nat) (month : Month) : Nat × Month :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def month_difference (m1 m2 : Month) : Nat :=
  sorry

theorem half_birthday_returns_valid_date (day : Nat) (month : Month)
  (h1 : 0 < day) (h2 : day ≤ daysInMonth month) :
  let (resultDay, resultMonth) := find_half_birthday day month
  0 < resultDay ∧ resultDay ≤ daysInMonth resultMonth :=
  sorry

theorem half_birthday_approximately_six_months (day : Nat) (month : Month) 
  (h1 : 0 < day) (h2 : day ≤ daysInMonth month) :
  let (_, resultMonth) := find_half_birthday day month
  let diff := month_difference month resultMonth  
  5 ≤ diff ∧ diff ≤ 7 :=
  sorry

-- Apps difficulty: interview
-- Assurance level: guarded