Tom  has finally taken over the business empire and now looking for 
a new Name of the business to make a new start.

Joe  (Tom's dear friend)  suggested a string $S$  consisting of
Uppercase and lowercase letters   

Tom wants to make some changes as per the following criteria:

1) String should $not$ have any vowels .

2) Every other uppercase consonant(other characters except vowels) should 
be in lowercase

For ex:

If the consonant character is Z then it should be z

3)  There should be  a character "." before each consonant.

Help Tom to make the required Changes.

-----Input:-----
- First line will contain string  $S$,This string only consists of uppercase and lowercase letters.

-----Output:-----
Print the resulting string. It is guaranteed that this string is not empty.

-----Constraints-----
- Length of string is in [1 .. 100]

-----Sample Input:-----
$CodeSprInT$

-----Sample Output:-----
.c.d.s.p.r.n.t 

-----EXPLANATION:-----
C is a consonant and it is in uppercase so turn it in lower case and add a “.” before it
o is a vowel so it is deleted
d  is a consonant and in lowercase so just  add a “.” before it
e  is a vowel so it is deleted
S is a consonant and it is in uppercase so turn it in lower case and add a “.” before it
p is a consonant and in lowercase so just  add a “.” before it
r is a consonant and in lowercase so just  add a “.” before it
I is a vowel so it is deleted
n is a consonant and in lowercase so just  add a “.” before it
T is a consonant and it is in uppercase so turn it in lower case and add a “.” before it

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible