/-
## Witamy!

You are in Poland and want to order a drink. You need to ask "One beer please": "Jedno piwo poprosze"

``` java
Translator.orderingBeers(1) = "Jedno piwo poprosze"
```

But let's say you are really thirsty and want several beers. Then you need to count in Polish. And more difficult, you need to understand the Polish grammar and cases (nominative, genitive, accustative and more).

## The grammar

In English, the plural of "beer" is simply "beers", with an "s". 

In Polish, the plural of "piwo" (nominative singular) is "piw" (genitive plural) or "piwa" (nominative plural). It depends!

The rules:

* usually the plural is genitive: "piw"
* but after the numerals 2, 3, 4, and compound numbers ending with them (e.g. 22, 23, 24), the noun is plural and takes the same case as the numeral, so nominative: "piwa"
* and exception to the exception: for 12, 13 and 14, it's the genitive plural again: "piw" (yes, I know, it's crazy!)

## The numbers

From 0 to 9:

    "zero", "jeden", "dwa", "trzy", "cztery", "piec", "szesc" , "siedem", "osiem", "dziewiec"

From 10 to 19 it's nearly the same, with "-ascie" at the end:

    "dziesiec", "jedenascie", "dwanascie", "trzynascie", "czternascie", "pietnascie", "szesnascie", "siedemnascie", "osiemnascie", "dziewietnascie"

Tens from 10 to 90 are nearly the same, with "-ziesci" or "ziesiat" at the end:

    "dziesiec", "dwadziescia", "trzydziesci", "czterdziesci", "piecdziesiat", "szescdziesiat", "siedemdziesiat", "osiemdziesiat", "dziewiecdziesiat"

Compound numbers are constructed similarly to English: tens + units. For example, 22 is "dwadziescia dwa".

"One" could be male ("Jeden"), female ("Jedna") or neuter ("Jedno"), which is the case for "beer" (piwo). But all other numbers are invariant, even if ending with "jeden".

Ah, and by the way, if you don't want to drink alcohol (so no beers are ordered), ask for mineral water instead: "Woda mineralna".

Note: if the number of beers is outside your (limited) Polish knowledge (0-99), raise an error!

---
More about the crazy polish grammar: https://en.wikipedia.org/wiki/Polish_grammar
-/

-- <vc-helpers>
-- </vc-helpers>

def ordering_beers (beers : Int) : String := sorry

theorem ordering_beers_zero :
  ordering_beers 0 = "Woda mineralna poprosze" := sorry

theorem ordering_beers_one :
  ordering_beers 1 = "Jedno piwo poprosze" := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible