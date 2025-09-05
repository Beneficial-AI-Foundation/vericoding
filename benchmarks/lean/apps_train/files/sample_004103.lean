**Story**  
On some island lives a chameleon population. Chameleons here can be of only one of three colors - red, green and blue. Whenever two chameleons of different colors meet, they can change their colors to a third one (i.e. when red and blue chameleons meet, they can both become green). There is no other way for chameleons to change their color (in particular, when red and blue chameleons meet, they can't become both red, only third color can be assumed).  
Chameleons want to become of one certain color. They may plan they meetings to reach that goal. Chameleons want to know, how fast their goal can be achieved (if it can be achieved at all).

**Formal problem**  
*Input:*  
Color is coded as integer, 0 - red, 1 - green, 2 - blue.
Chameleon starting population is given as an array of three integers, with index corresponding to color (i.e. [2, 5, 3] means 2 red, 5 green and 3 blue chameleons). All numbers are non-negative, their sum is between `1` and `int.MaxValue` (maximal possible value for `int` type, in other languages). Desired color is given as an integer from 0 to 2.  
*Output:*  
`Kata.Chameleon` should return *minimal* number of meetings required to change all chameleons to a given color, or -1 if it is impossible (for example, if all chameleons are initially of one other color).  

**Notes and hints**  
-- Some tests use rather big input values. Be effective.  
-- There is a strict proof that answer is either -1 or no greater than total number of chameleons (thus, return type `int` is justified). Don't worry about overflow.  

**Credits**  
Kata based on "Chameleons" puzzle from braingames.ru: http://www.braingames.ru/?path=comments&puzzle=226 (russian, not translated).

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded