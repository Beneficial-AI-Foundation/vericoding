Reading books is one of Sasha's passions. Once while he was reading one book, he became acquainted with an unusual character. The character told about himself like that: "Many are my names in many countries. Mithrandir among the Elves, Tharkûn to the Dwarves, Olórin I was in my youth in the West that is forgotten, in the South Incánus, in the North Gandalf; to the East I go not."

And at that moment Sasha thought, how would that character be called in the East? In the East all names are palindromes. A string is a palindrome if it reads the same backward as forward. For example, such strings as "kazak", "oo" and "r" are palindromes, but strings "abb" and "ij" are not. 

Sasha believed that the hero would be named after one of the gods of the East. As long as there couldn't be two equal names, so in the East people did the following: they wrote the original name as a string on a piece of paper, then cut the paper minimum number of times $k$, so they got $k+1$ pieces of paper with substrings of the initial string, and then unite those pieces together to get a new string. Pieces couldn't be turned over, they could be shuffled.

In this way, it's possible to achive a string abcdefg from the string f|de|abc|g using $3$ cuts (by swapping papers with substrings f and abc). The string cbadefg can't be received using the same cuts.

More formally, Sasha wants for the given palindrome $s$ find such minimum $k$, that you can cut this string into $k + 1$ parts, and then unite them in such a way that the final string will be a palindrome and it won't be equal to the initial string $s$. It there is no answer, then print "Impossible" (without quotes).

-----Input-----

The first line contains one string $s$ ($1 \le |s| \le 5\,000$) — the initial name, which consists only of lowercase Latin letters. It is guaranteed that $s$ is a palindrome.

-----Output-----

Print one integer $k$ — the minimum number of cuts needed to get a new name, or "Impossible" (without quotes).

-----Examples-----
Input
nolon

Output
2

Input
otto

Output
1

Input
qqqq

Output
Impossible

Input
kinnikkinnik

Output
1

-----Note-----

In the first example, you can cut the string in those positions: no|l|on, and then unite them as follows on|l|no. It can be shown that there is no solution with one cut.

In the second example, you can cut the string right in the middle, and swap peaces, so you get toot.

In the third example, you can't make a string, that won't be equal to the initial one.

In the fourth example, you can cut the suffix nik and add it to the beginning, so you get nikkinnikkin.

def is_palindrome (s : String) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
