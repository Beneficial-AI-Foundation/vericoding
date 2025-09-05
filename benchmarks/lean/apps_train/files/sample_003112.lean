In this Kata, two players, Alice and Bob, are playing a palindrome game. Alice starts with `string1`, Bob starts with `string2`, and the board starts out as an empty string. Alice and Bob take turns; during a turn, a player selects a letter from his or her string, removes it from the string, and appends it to the board; if the board becomes a palindrome (of length >= 2), the player wins. Alice makes the first move. Since Bob has the disadvantage of playing second, then he wins automatically if letters run out or the board is never a palindrome. Note also that each player can see the other player's letters.

The problem will be presented as `solve(string1,string2)`. Return 1 if Alice wins and 2 it Bob wins.

For example:
```Haskell
solve("abc","baxy") = 2 -- There is no way for Alice to win. If she starts with 'a', Bob wins by playing 'a'. The same case with 'b'. If Alice starts with 'c', Bob still wins because a palindrome is not possible. Return 2.
solve("eyfjy","ooigvo") = 1 -- Alice plays 'y' and whatever Bob plays, Alice wins by playing another 'y'. Return 1.
solve("abc","xyz") = 2 -- No palindrome is possible, so Bob wins; return 2
solve("gzyqsczkctutjves","hpaqrfwkdntfwnvgs") = 1 -- If Alice plays 'g', Bob wins by playing 'g'. Alice must be clever. She starts with 'z'. She knows that since she has two 'z', the win is guaranteed. Note that she also has two 's'. But she cannot play that. Can you see why? 
solve("rmevmtw","uavtyft") = 1 -- Alice wins by playing 'm'. Can you see why? 
```
Palindrome lengths should be at least `2` characters. More examples in the test cases. 

Good luck!

def solve (s1 s2 : String) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
