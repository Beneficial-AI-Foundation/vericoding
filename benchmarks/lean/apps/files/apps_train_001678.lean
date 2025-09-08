/-
Print an ordered cross table of a round robin tournament that looks like this:

```
 #  Player            1  2  3  4  5  6  7  8  9 10 11 12 13 14  Pts   SB
==========================================================================
 1  Nash King            1  0  =  1  0  =  1  1  0  1  1  1  0  8.0  52.25
 2  Karsyn Marks      0     1  1  =  1  =  =  1  0  0  1  1  0  7.5  49.75
 3  Yandel Briggs     1  0     =  0  =  1  1  1  =  0  1  0  1  7.5  47.25
    Luka Harrell      =  0  =     1  1  1  =  0  0  1  1  0  1  7.5  47.25
    Pierre Medina     0  =  1  0     =  1  =  1  1  =  0  1  =  7.5  47.25
 6  Carlos Koch       1  0  =  0  =     =  =  1  1  =  0  =  1  7.0  43.50
 7  Tristan Pitts     =  =  0  0  0  =     1  0  1  =  1  1  1  7.0  40.75
    Luke Schaefer     0  =  0  =  =  =  0     1  =  =  1  1  1  7.0  40.75
 9  Tanner Dunn       0  0  0  1  0  0  1  0     1  1  =  1  1  6.5  37.25
10  Haylee Bryan      1  1  =  1  0  0  0  =  0     1  0  0  1  6.0  39.25
11  Dylan Turner      0  1  1  0  =  =  =  =  0  0     1  =  =  6.0  38.75
12  Adyson Griffith   0  0  0  0  1  1  0  0  =  1  0     1  1  5.5  31.75
13  Dwayne Shaw       0  0  1  1  0  =  0  0  0  1  =  0     1  5.0  30.50
14  Kadin Rice        1  1  0  0  =  0  0  0  0  0  =  0  0     3.0  22.25
```

The `#` column contains the rank. Ranks may be tied.  
A colum with index numbers `i` contains the match against the player on line `i`. `1` / `=` / `0` means win / draw / loss.  
The `Pts` column contains the score, 1 for each win, 0.5 for each draw.  
The `SB` column contains the Sonneborn-Berger score (see below).  

The rank is determined by the score, the Sonneborn-Berger score is used to break ties.
Players with the same score and the same SB score share the same rank.
In the cross table those tied players are ordered by their surenames.

# Sonneborn-Berger score

The Sonneborn-Berger score (`SB`) (sometimes also called Neustadtl Sonneborn–Berger or Neustadtl score) is a system to break ties in tournaments.
This score is based on the observation that it is usually harder to score against higher ranked than against lower ranked opponents.
The score is the sum of the points of opponents this player has defeated plus the half the sum of the points of opponents this player has drawn against.
For examples, see the table above.

# Task

Write a function `crosstable(players, results)`.

Input:
* `players`: a list of names (`["Forename Surename", ...]`)
* `results`: a list of lists of results, where result may be `1`, `0.5`, `0` or `None`.

Output:

* The cross table as a string.  
  There is no whitespace at the end of the lines.  
  The columns are separated by two spaces.  
  The column headers for the rank (`#`) and for the rounds are right adjusted, `Players` is left-adjusted, `Pts` and `SB` are centered.  
  The separator line consisting of `=` is just as long as the longest line in the output.

# Examples

```python
d, _ = 0.5, None

crosstable([
    'Emmett Frost', 'Cruz Sullivan', 'Deandre Bullock', 'George Bautista', 'Norah Underwood', 'Renee Preston'], [
    [_, 1, 0, 0, d, 0],
    [0, _, d, 1, 0, 0],
    [1, d, _, d, d, d],
    [1, 0, d, _, d, d],
    [d, 1, d, d, _, d],
    [1, 1, d, d, d, _]])

# returns
'''\
#  Player           1 2 3 4 5 6  Pts   SB
==========================================
1  Renee Preston      = = = 1 1  3.5  7.25
2  Deandre Bullock  =   = = = 1  3.0  6.75
   Norah Underwood  = =   = 1 =  3.0  6.75
4  George Bautista  = = =   0 1  2.5  6.25
5  Cruz Sullivan    0 = 0 1   0  1.5  4.00
6  Emmett Frost     0 0 = 0 1    1.5  3.00'''

crosstable([
    'Luke Schaefer', 'Adyson Griffith', 'Dylan Turner', 'Carlos Koch', 'Luka Harrell', 'Karsyn Marks', 'Haylee Bryan',
    'Dwayne Shaw', 'Pierre Medina', 'Nash King', 'Kadin Rice', 'Tristan Pitts', 'Tanner Dunn', 'Yandel Briggs'], [
    [_, 1, d, d, d, d, d, 1, d, 0, 1, 0, 1, 0],
    [0, _, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, d, 0],
    [d, 1, _, d, 0, 1, 0, d, d, 0, d, d, 0, 1],
    [d, 0, d, _, 0, 0, 1, d, d, 1, 1, d, 1, d],
    [d, 1, 1, 1, _, 0, 0, 0, 1, d, 1, 1, 0, d],
    [d, 1, 0, 1, 1, _, 0, 1, d, 0, 0, d, 1, 1],
    [d, 0, 1, 0, 1, 1, _, 0, 0, 1, 1, 0, 0, d],
    [0, 0, d, d, 1, 0, 1, _, 0, 0, 1, 0, 0, 1],
    [d, 0, d, d, 0, d, 1, 1, _, 0, d, 1, 1, 1],
    [1, 1, 1, 0, d, 1, 0, 1, 1, _, 0, d, 1, 0],
    [0, 0, d, 0, 0, 1, 0, 0, d, 1, _, 0, 0, 0],
    [1, 1, d, d, 0, d, 1, 1, 0, d, 1, _, 0, 0],
    [0, d, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, _, 0],
    [1, 1, 0, d, d, 0, d, 0, 0, 1, 1, 1, 1, _]])

# returns
'''\
 #  Player            1  2  3  4  5  6  7  8  9 10 11 12 13 14  Pts   SB
==========================================================================
 1  Nash King            1  0  =  1  0  =  1  1  0  1  1  1  0  8.0  52.25
 2  Karsyn Marks      0     1  1  =  1  =  =  1  0  0  1  1  0  7.5  49.75
 3  Yandel Briggs     1  0     =  0  =  1  1  1  =  0  1  0  1  7.5  47.25
    Luka Harrell      =  0  =     1  1  1  =  0  0  1  1  0  1  7.5  47.25
    Pierre Medina     0  =  1  0     =  1  =  1  1  =  0  1  =  7.5  47.25
 6  Carlos Koch       1  0  =  0  =     =  =  1  1  =  0  =  1  7.0  43.50
 7  Tristan Pitts     =  =  0  0  0  =     1  0  1  =  1  1  1  7.0  40.75
    Luke Schaefer     0  =  0  =  =  =  0     1  =  =  1  1  1  7.0  40.75
 9  Tanner Dunn       0  0  0  1  0  0  1  0     1  1  =  1  1  6.5  37.25
10  Haylee Bryan      1  1  =  1  0  0  0  =  0     1  0  0  1  6.0  39.25
11  Dylan Turner      0  1  1  0  =  =  =  =  0  0     1  =  =  6.0  38.75
12  Adyson Griffith   0  0  0  0  1  1  0  0  =  1  0     1  1  5.5  31.75
13  Dwayne Shaw       0  0  1  1  0  =  0  0  0  1  =  0     1  5.0  30.50
14  Kadin Rice        1  1  0  0  =  0  0  0  0  0  =  0  0     3.0  22.25'''

crosstable([
    'Mikaela Orozco', 'Mekhi Mayer', 'Marcus Galvan', 'Leroy Wilkins', 'Gregory Bates', 'Jayda Lynn', 'Makena Galloway',
    'Adriel Brock', 'Morgan Gillespie', 'Darwin Mack', 'Clayton Terrell', 'Bo Schmidt', 'Xzavier Clements', 'Rex Cummings',
    'Aldo Jackson', 'Justus Sloan', 'Rudy Herrera', 'Leonard Ponce', 'Kaden Harding', 'Anastasia Dodson'], [
    [_, 1, 1, 0, 1, d, 1, 1, 0, 1, 0, d, 0, d, d, 0, d, 0, 0, d],
    [0, _, 0, d, d, 0, d, 1, d, d, 0, 1, 1, d, d, d, d, 1, d, 0],
    [0, 1, _, 0, 0, d, 1, d, 0, d, 0, d, 0, 1, 1, 0, 0, 0, 1, 1],
    [1, d, 1, _, d, 0, d, 0, d, 0, 1, d, 0, 0, 1, 0, d, 1, d, 1],
    [0, d, 1, d, _, 1, d, 1, 1, 1, d, 1, 1, d, 0, 1, 1, 1, d, d],
    [d, 1, d, 1, 0, _, 0, d, d, 1, d, 0, d, 0, 0, 0, 1, d, 1, 1],
    [0, d, 0, d, d, 1, _, 1, 1, 1, 1, 0, d, 0, 1, 1, d, 1, 1, 0],
    [0, 0, d, 1, 0, d, 0, _, 1, d, 0, d, 1, d, d, 1, d, 0, 0, 0],
    [1, d, 1, d, 0, d, 0, 0, _, 0, 1, 0, 0, 1, 1, d, d, 1, 0, 0],
    [0, d, d, 1, 0, 0, 0, d, 1, _, d, d, 1, 1, d, 0, 1, d, 1, d],
    [1, 1, 1, 0, d, d, 0, 1, 0, d, _, 1, d, 0, 0, d, 0, 0, d, d],
    [d, 0, d, d, 0, 1, 1, d, 1, d, 0, _, 1, d, d, 0, 1, 0, 0, 0],
    [1, 0, 1, 1, 0, d, d, 0, 1, 0, d, 0, _, 1, d, d, 0, 1, d, d],
    [d, d, 0, 1, d, 1, 1, d, 0, 0, 1, d, 0, _, d, 0, 0, 0, 1, 1],
    [d, d, 0, 0, 1, 1, 0, d, 0, d, 1, d, d, d, _, d, 1, 0, 1, 1],
    [1, d, 1, 1, 0, 1, 0, 0, d, 1, d, 1, d, 1, d, _, 1, 1, 0, d],
    [d, d, 1, d, 0, 0, d, d, d, 0, 1, 0, 1, 1, 0, 0, _, 0, 0, 1],
    [1, 0, 1, 0, 0, d, 0, 1, 0, d, 1, 1, 0, 1, 1, 0, 1, _, d, d],
    [1, d, 0, d, d, 0, 0, 1, 1, 0, d, 1, d, 0, 0, 1, 1, d, _, 0],
    [d, 1, 0, 0, d, 0, 1, 1, 1, d, d, 1, d, 0, 0, d, 0, d, 1, _]])

# returns
'''\
 #  Player             1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20  Pts     SB
===============================================================================================
 1  Gregory Bates         1  =  0  1  1  =  1  =  1  0  =  =  =  1  1  =  1  1  1  13.5  124.50
 2  Justus Sloan       0     0  =  1  1  =  =  1  1  1  1  =  0  =  1  =  1  1  0  12.0  109.00
 3  Makena Galloway    =  1     1  1  1  0  =  =  1  0  0  =  1  1  0  1  0  =  1  11.5  109.75
 4  Aldo Jackson       1  =  0     =  0  1  =  0  1  =  =  =  1  0  =  1  0  1  =  10.0   95.25
 5  Darwin Mack        0  0  0  =     =  =  1  1  0  0  1  =  1  1  =  =  =  1  =  10.0   89.00
 6  Leonard Ponce      0  0  0  1  =     =  0  0  =  1  1  0  =  0  1  1  1  1  1  10.0   87.50
 7  Anastasia Dodson   =  =  1  0  =  =     =  0  0  =  0  1  1  1  1  =  0  0  1   9.5   90.25
 8  Xzavier Clements   0  =  =  =  0  1  =     1  =  1  1  0  =  1  0  =  1  0  0   9.5   89.00
    Leroy Wilkins      =  0  =  1  0  1  1  0     0  1  0  =  =  =  =  1  1  =  0   9.5   89.00
10  Jayda Lynn         0  0  0  0  1  =  1  =  1     =  0  1  1  =  0  =  =  1  =   9.5   85.50
11  Mikaela Orozco     1  0  1  =  1  0  =  0  0  =     =  1  0  0  =  0  1  =  1   9.0   86.75
12  Rex Cummings       =  0  1  =  0  0  1  0  1  1  =     =  1  0  =  1  0  0  =   9.0   86.25
13  Mekhi Mayer        =  =  =  =  =  1  0  1  =  0  0  =     =  =  1  0  0  =  1   9.0   86.00
14  Kaden Harding      =  1  0  0  0  =  0  =  =  0  1  0  =     1  1  =  0  1  1   9.0   83.50
15  Morgan Gillespie   0  =  0  1  0  1  0  0  =  =  1  1  =  0     0  1  1  =  0   8.5   78.50
    Bo Schmidt         0  0  1  =  =  0  0  1  =  1  =  =  0  0  1     0  =  1  =   8.5   78.50
    Clayton Terrell    =  =  0  0  =  0  =  =  0  =  1  0  1  =  0  1     1  0  1   8.5   78.50
18  Marcus Galvan      0  0  1  1  =  0  1  0  0  =  0  1  1  1  0  =  0     0  =   8.0   75.75
19  Rudy Herrera       0  0  =  0  0  0  1  1  =  0  =  1  =  0  =  0  1  1     =   8.0   72.00
20  Adriel Brock       0  1  0  =  =  0  0  1  1  =  0  =  0  0  1  =  0  =  =      7.5   71.00'''
```
-/

-- <vc-helpers>
-- </vc-helpers>

def sumDigits (n : Int) : Int := sorry

theorem sum_digits_non_negative (n : Int) :
  sumDigits n ≥ 0 := sorry

theorem sum_digits_abs_equal (n : Int) :
  sumDigits n = sumDigits (Int.natAbs n) := sorry

theorem sum_digits_less_than_input (n : Int) :
  Int.natAbs n > 9 → sumDigits n < Int.natAbs n := sorry

-- Note: The last property about matching sum of individual digits
-- would require additional string manipulation and digit conversion definitions,
-- so we'll just state it in terms of natural recursion

theorem sum_digits_equals_digit_sum (n : Int) :
  sumDigits n = sumDigits (n / 10) + n % 10 := sorry

-- Apps difficulty: interview
-- Assurance level: guarded