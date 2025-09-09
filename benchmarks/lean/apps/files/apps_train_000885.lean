/-
Recently, Chef got obsessed with piano. He is a just a rookie in this stuff and can not move his fingers from one key to other fast enough. He discovered that the best way to train finger speed is to play scales.

There are different kinds of scales which are divided on the basis of their interval patterns. For instance, major scale is defined by pattern T-T-S-T-T-T-S, where ‘T’ stands for a whole tone whereas ‘S’ stands for a semitone. Two semitones make one tone. To understand how they are being played, please refer to the below image of piano’s octave – two consecutive keys differ by one semitone.

If we start playing from first key (note C), then we’ll play all white keys in a row (notes C-D-E-F-G-A-B-C – as you can see C and D differ for a tone as in pattern, and E and F differ for a semitone).

This pattern could be played some number of times (in cycle).

Each time Chef takes some type of a scale and plays using some number of octaves. Sometimes Chef can make up some scales, so please don’t blame him if you find some scale that does not exist in real world.

Formally, you have a set of 12 keys (i.e. one octave) and you have N such sets in a row. So in total, you have 12*N keys. You also have a pattern that consists of letters 'T' and 'S', where 'T' means move forward for two keys (from key x to key x + 2, and 'S' means move forward for one key (from key x to key x + 1).

Now, you can start playing from any of the 12*N keys. In one play, you can repeat the pattern as many times as you want, but you cannot go outside the keyboard.

Repeating pattern means that if, for example, you have pattern STTST, you can play STTST as well as STTSTSTTST, as well as STTSTSTTSTSTTST, as well as any number of repeating. For this pattern, if you choose to repeat it once, if you start at some key x, you'll press keys: x (letter 'S')-> x + 1 (letter 'T')-> x + 3 (letter 'T')-> x + 5 (letter 'S') -> x + 6 (letter 'T')-> x + 8. Also 1 ≤ x, x + 8 ≤ 12*N so as to avoid going off the keyboard.

You are asked to calculate number of different plays that can be performed. Two plays differ if and only if they start at different keys or patterns are repeated different number of times.

-----Input-----
The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows.

First line of each test case contains scale’s pattern – string s consisting of letters ‘T’ and ‘S’ only.

Second line contains one integer N – number of octaves he’ll be using.

-----Output-----
For each test case output a single number in a line corresponding to number of different scales he’ll play. 

-----Constraints-----
- 1 ≤ T ≤ 105
- 1 ≤ |S| ≤ 100
- 1 ≤ n ≤ 7

-----Subtasks-----
Subtask 1: T < 10 4, N = 1 
Subtask 2: No additional constraints.

-----Example-----
Input:
2 
TTTT
1
TTSTTTS
3

Output:
4
36

-----Explanation-----
Example case 1. In the first case there is only one octave and Chef can play scale (not in cycle each time) starting with notes C, C#, D, D# - four together.
-/

def Scale := String
def C : Scale := "C"

def TS : Scale := "TS"

instance : DecidableEq Scale := 
  fun x y => match x, y with
  | s1, s2 => String.decEq s1 s2

-- <vc-helpers>
-- </vc-helpers>

def calculate_scale_plays (scale_type : Scale) (octaves : Nat) : Nat :=
  sorry

theorem calculate_scale_plays_positive 
  (scale_type : Scale)
  (octaves : Nat)
  (h1 : scale_type = C ∨ scale_type = TS)
  (h2 : octaves ≥ 1)
  (h3 : octaves ≤ 100) :
  calculate_scale_plays scale_type octaves > 0 :=
sorry

theorem calculate_scale_plays_formula 
  (scale_type : Scale)
  (octaves : Nat)
  (h1 : scale_type = C ∨ scale_type = TS)
  (h2 : octaves ≥ 1)
  (h3 : octaves ≤ 100) :
  calculate_scale_plays scale_type octaves = 
    (if scale_type = C then 7 else 11) * octaves - 1 :=
sorry

theorem calculate_scale_plays_invalid
  (scale_type : Scale)
  (octaves : Nat)  
  (h : scale_type ≠ C ∧ scale_type ≠ TS) :
  ¬∃ (result : Nat), calculate_scale_plays scale_type octaves = result :=
sorry

/-
info: 13
-/
-- #guard_msgs in
-- #eval calculate_scale_plays "C" 2

/-
info: 21
-/
-- #guard_msgs in
-- #eval calculate_scale_plays "TS" 2

-- Apps difficulty: interview
-- Assurance level: guarded