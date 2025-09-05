Once upon a time, a CodeWarrior, after reading a [discussion on what can be the plural](http://www.codewars.com/kata/plural/discuss/javascript), took a look at [this page](http://en.wikipedia.org/wiki/Grammatical_number#Types_of_number
) and discovered that **more than 1** "kind of plural" may exist. 

For example [Sursurunga Language](http://en.wikipedia.org/wiki/Sursurunga_language) distinguishes 5 types of numbers: **singular** (1 thing), **dual** (2 things), '**trial**' or '**lesser paucal**' (3 or 4), '**greater paucal**' (more than 4) and **plural** (many).

In this kata, you'll have to handle only four types of numbers:

- **singular**: 0 or 1 thing
- **dual**: 2 things
- **paucal**: 3 to 9 things
- **plural**: more than 9 things

To add some flavor the **number-marker** will not be added in same places:

- **singular**, no marker : `1 cat`
- **dual**, prefixed "`bu`" : `2 cats -> 2 bucat`
- **paucal**, suffixed "`zo`" : `4 cats -> 4 catzo`
- **plural**, "circumfixed `ga`" : `100 cats -> 100 gacatga`

As you all ("hawk eyes") have seen, the final `s` of english plural **disappears**.

( btw these markers, of course, have absolutely nothing to do with true sursurunga language, we're just talking about "**pig**-sursurunga" with **pig** as **pig** in "**pig latin**" )

## Your Job . . .
. . . if you accept it, will be to write a `sursurungal` function which get a `string` as argument and returns this string with words in it eventually converted to their "pig-sursurunga number type".

If a `number` ( *ie* 1 or more digit ) + a `space` + a `word` ( letters ) are found then the word should be converted.

**Each** group of `number+space+word` found in the string should be evaluated.

### Examples :

You may assume at least 1 `number+space+word` group will be provided.

**Beware** `s` of english plural should be removed, not ending `s` of some singular words ( *eg* "kiss" )

Good luck!

def sursurungal (s : String) : String := sorry
def containsDigit (s : String) (d : Nat) : Prop := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
