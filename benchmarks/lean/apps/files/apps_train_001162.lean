/-
Mark loves eating chocolates and also likes to be fit. Given the calorie count for every chocolate he eats, find what he has to do to burn the calories. 
The name of the chocolates along with its calorie count are given as follows:
Calories per one whole bar:
Dairy milk (D)
238
Twix (T)
244
Milky Bar (M)
138
Bounty (B)
279
Crunchie (C)
186
The exercises preferred by him and the calories burnt are as follows:
Calories burnt per km:
Running
50
Cycling
5
Walking
0.5
Find the number of kilometers he has to run, cycle or walk to burn all of the calories. 
Priority given to the exercises is as follows: 
Running > Cycling > Walking

-----Input:-----
- It is a one line string consisting of the names(initial letter) of all the chocolates he has eaten.

-----Output:-----
Print three lines. First line representing how much he ran(in km), second line representing how much he cycled(in km), third line representing how much he walked(in km).

-----Constraints-----
- 1 <= length of input string <= 10. 

-----Sample Input:-----
DDTM

-----Sample Output:-----
17
1
6

-----EXPLANATION:-----
Calorie intake = 238 + 238 + 244 + 138 = 858
( 17km x 50 ) + ( 1km x 5 ) + ( 6km x 0.5 ) = 858.
-/

def isUpper (c : Char) : Bool := sorry
def isDigit (c : Char) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def isSpace (c : Char) : Bool := sorry

def count_elements (s : String) : Nat × Nat × Nat := sorry

theorem count_elements_totals (s : String) :
  let (uppers, digits, spaces) := count_elements s
  let total := uppers + digits + spaces
  total ≤ s.length := 
sorry

theorem empty_string :
  count_elements "" = (0, 0, 0) :=
sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible