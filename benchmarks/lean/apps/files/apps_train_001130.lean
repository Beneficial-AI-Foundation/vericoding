/-
This is a simple game you must have played around with during your school days, calculating FLAMES of you and your crush! Given the names of two people, cancel out the common letters (repeated occurrence of a letter is treated separately, so 2A's in one name and one A in the other would cancel one A in each name), count the total number of remaining letters (n) and repeatedly cut the letter in the word FLAMES which hits at the nth number when we count from F in cyclic manner.

For example:
NAME 1: SHILPA
NAME 2: AAMIR
After cutting the common letters: 
NAME 1: SHILPA 
NAME 2: AAMIR
Total number of letters left=7
FLAMES, start counting from F : 1=F, 2=L, 3=A, 4=M, 5=E, 6=S,7=F...So cut F
FLAMES: repeat this process with remaining letters of FLAMES for number 7 (start count from the letter after 
the last letter cut) . In the end, one letter remains. Print the result corresponding to the last letter:
F=FRIENDS
L=LOVE
A=ADORE
M=MARRIAGE
E=ENEMIES
S=SISTER

-----Input-----
The no. of test cases (<100)
two names (may include spaces) for each test case.

-----Output-----
FLAMES result (Friends/Love/...etc) for each test case

-----Example-----
Input:
2
SHILPA
AAMIR
MATT
DENISE

Output:
ENEMIES
LOVE

By:
Chintan, Asad, Ashayam, Akanksha
-/

-- <vc-helpers>
-- </vc-helpers>

def ValidResult := ["FRIENDS", "LOVE", "ADORE", "MARRIAGE", "ENEMIES", "SISTER"]

def calculate_flames (name1 : String) (name2 : String) : String :=
  sorry

theorem calculate_flames_symmetry (name1 name2 : String) :
  name1 ≠ "" → name2 ≠ "" →
  calculate_flames name1 name2 = calculate_flames name2 name1 :=
sorry

theorem calculate_flames_whitespace_invariant (name : String) :
  name ≠ "" →
  calculate_flames name "test" = calculate_flames (name ++ "  ") "test" ∧
  calculate_flames name "test" = calculate_flames (" " ++ name ++ " ") "test" :=
sorry

theorem calculate_flames_identical_names (name : String) :
  name ≠ "" →
  calculate_flames name name = calculate_flames "a" "a" :=
sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible