/-
# Number encrypting: cypher
## Part I of Number encrypting Katas
***

## Introduction
Back then when the internet was coming up, most search functionalities simply looked for keywords in text to show relevant documents. Hackers weren't very keen on having their information displayed on websites, bulletin boards, newsgroups or any other place, so they started to replace certain letters in words. It started out with simple vowel substitutions like a 4 instead of an A, or a 3 instead of an E. This meant that topics like cracking or hacking remained undetected.

Here we will use a reduced version of the *Leet Speak alphabet*, but you can find more information [here](http://www.gamehouse.com/blog/leet-speak-cheat-sheet/) or at [Wikipedia](https://en.wikipedia.org/wiki/Leet).

## Task
You will receive a string composed by English words, `string`. You will have to return a cyphered version of that string.

The numbers corresponding to each letter are represented at the table below. Notice that different letters can share the same number. In those cases, one letter will be upper case and the other one lower case.

  .cell {
    border: 1px solid white;
    text-align: center;
    width: 7%;
  }

  .title {
    border: 1px solid white;
    border-bottom: 1px solid white;
    text-align: center;
    min-width: 11em;
  }

  .no-border {border: none}

  table {
    margin-bottom: 10px
  }

    1
    2
    3
    4
    5
    6
    7
    8
    9
    0

    Upper case
    I
    R
    E
    A
    S
    G
    T
    B

    O

    Lower case
    l
    z
    e
    a
    s
    b
    t

    g
    o

Any character that is not at the table, does not change when cyphered.

## Examples

  * **Input:** "Hello World". **Output**: "H3110 W0r1d"
  * **Input:** "I am your father". **Output**: "1 4m y0ur f47h3r"
  * **Input:** "I do not know what else I can test. Be cool. Good luck". **Output**: "1 d0 n07 kn0w wh47 3153 1 c4n 7357. 83 c001. 600d 1uck"

## Part II
If you liked this Kata, you can find the [part II: *Number encrypting: decypher*](https://www.codewars.com/kata/number-encrypting-decypher), where your goal is to decypher the strings.
-/

-- <vc-helpers>
-- </vc-helpers>

def cypher (s : String) : String := sorry

theorem cypher_length_preserved (s : String) : 
  (cypher s).length = s.length := sorry

theorem cypher_idempotent (s : String) :
  cypher (cypher s) = cypher s := sorry

theorem cypher_maps_chars_correctly (s : String) :
  cypher s = s.map (fun c => match c with
    | 'I' => '1' | 'R' => '2' | 'E' => '3' | 'A' => '4' 
    | 'S' => '5' | 'G' => '6' | 'T' => '7' | 'B' => '8'
    | 'l' => '1' | 'z' => '2' | 'e' => '3' | 'a' => '4'
    | 's' => '5' | 'b' => '6' | 't' => '7' | 'g' => '9'
    | 'o' => '0' | 'O' => '0'
    | c => c) := sorry

theorem cypher_preserves_unmapped (s : String) (c : Char) :
  c ∉ ['I', 'R', 'E', 'A', 'S', 'G', 'T', 'B', 'l', 'z', 'e', 'a', 's', 'b', 't', 'g', 'o', 'O'] →
  (c ∈ s.data → c ∈ (cypher s).data) := sorry

/-
info: 'H3110 W0r1d'
-/
-- #guard_msgs in
-- #eval cypher "Hello World"

/-
info: '1 4m y0ur f47h3r'
-/
-- #guard_msgs in
-- #eval cypher "I am your father"

/-
info: '1 d0 n07 kn0w wh47 3153 1 c4n 7357. 83 c001. 600d 1uck'
-/
-- #guard_msgs in
-- #eval cypher "I do not know what else I can test. Be cool. Good luck"

-- Apps difficulty: introductory
-- Assurance level: unguarded