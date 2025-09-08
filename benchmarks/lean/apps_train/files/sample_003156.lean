/-
###Introduction

The [I Ching](https://en.wikipedia.org/wiki/I_Ching) (Yijing, or Book of Changes) is an ancient Chinese book of sixty-four hexagrams. 
A hexagram is a figure composed of six stacked horizontal lines, where each line is either Yang (an unbroken line) or Yin (a broken line):
```
---------    ---- ----    ---------    
---- ----    ---- ----    ---------    
---- ----    ---- ----    ---------    
---------    ---- ----    ---- ----    
---------    ---------    ---- ----    
---- ----    ---- ----    ---------    
```
The book is commonly used as an oracle. After asking it a question about one's present scenario,
each line is determined by random methods to be Yang or Yin. The resulting hexagram is then interpreted by the querent as a symbol of their current situation, and how it might unfold.

This kata will consult the I Ching using the three coin method.

###Instructions

A coin is flipped three times and lands heads
or tails. The three results are used to
determine a line as being either:
```
3 tails          ----x----  Yin (Moving Line*)
2 tails 1 heads  ---------  Yang
1 tails 2 heads  ---- ----  Yin 
3 heads          ----o----  Yang (Moving Line*)

*See bottom of description if curious.
```
This process is repeated six times to determine
each line of the hexagram. The results of these
operations are then stored in a 2D Array like so:
In each array the first index will always be the number of the line ('one' is the bottom line, and 'six' the top), and the other three values will be the results of the coin flips that belong to that line as heads ('h') and tails ('t').

Write a function that will take a 2D Array like the above as argument and return its hexagram as a string. Each line of the hexagram should begin on a new line.

should return:
```
---------
---------
----x----
----o----
---- ----
---- ----
```
You are welcome to consult your new oracle program with a question before pressing submit. You can compare your result [here](http://www.ichingfortune.com/hexagrams.php). The last test case is random and can be used for your query.

*[1] A Moving Line is a Yang line that will change
to Yin or vice versa. The hexagram made by the coin
throws represents the querent's current situation,
and the hexagram that results from changing its
moving lines represents their upcoming situation.*
-/

def oracle (input : List (LineName × CoinFlip × CoinFlip × CoinFlip)) : List LineOutput :=
  sorry

def getOutput (output : List LineOutput) (line : LineName × CoinFlip × CoinFlip × CoinFlip) : LineOutput :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def sortFlips (f1 f2 f3 : CoinFlip) : CoinFlip × CoinFlip × CoinFlip :=
  sorry

theorem oracle_output_length {input : List (LineName × CoinFlip × CoinFlip × CoinFlip)} 
  (h1 : input.length = 6)
  (h2 : ∀ x y, x ∈ input → y ∈ input → x.1 = y.1 → x = y) :
  (oracle input).length = 6 := 
  sorry

theorem line_positions_valid {input : List (LineName × CoinFlip × CoinFlip × CoinFlip)}
  (h1 : input.length = 6)
  (h2 : ∀ x y, x ∈ input → y ∈ input → x.1 = y.1 → x = y) :
  ∀ line, line ∈ input → ∃ pos, pos < 6 :=
  sorry

theorem oracle_flip_mapping {input : List (LineName × CoinFlip × CoinFlip × CoinFlip)}
  (h1 : input.length = 6)
  (h2 : ∀ x y, x ∈ input → y ∈ input → x.1 = y.1 → x = y)
  (line : LineName × CoinFlip × CoinFlip × CoinFlip) 
  (h3 : line ∈ input) :
  let (name, f1, f2, f3) := line
  let (s1, s2, s3) := sortFlips f1 f2 f3
  if s1 = CoinFlip.H ∧ s2 = CoinFlip.H ∧ s3 = CoinFlip.H then
    getOutput (oracle input) line = LineOutput.Circle
  else if s1 = CoinFlip.T ∧ s2 = CoinFlip.T ∧ s3 = CoinFlip.T then
    getOutput (oracle input) line = LineOutput.X
  else if s1 = CoinFlip.H ∧ s2 = CoinFlip.H ∧ s3 = CoinFlip.T then
    getOutput (oracle input) line = LineOutput.Space
  else if s1 = CoinFlip.H ∧ s2 = CoinFlip.T ∧ s3 = CoinFlip.T then
    getOutput (oracle input) line = LineOutput.Empty
  else
    True :=
  sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval oracle [["two", "h", "h", "t"], ["six", "t", "h", "t"], ["four", "t", "t", "t"], ["one", "h", "t", "h"], ["three", "h", "h", "h"], ["five", "t", "t", "h"]]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval oracle [["six", "t", "t", "h"], ["one", "h", "h", "t"], ["three", "t", "h", "h"], ["two", "t", "t", "t"], ["five", "h", "h", "t"], ["four", "t", "t", "h"]]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval oracle [["five", "h", "h", "h"], ["four", "t", "t", "h"], ["two", "h", "t", "h"], ["one", "h", "h", "t"], ["six", "t", "h", "t"], ["three", "h", "h", "h"]]

-- Apps difficulty: introductory
-- Assurance level: unguarded