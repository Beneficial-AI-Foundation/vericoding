Taking into consideration the [3.5 edition rules](http://www.dandwiki.com/wiki/SRD:Ability_Scores#Table:_Ability_Modifiers_and_Bonus_Spells), your goal is to build a function that takes an ability score (worry not about validation: it is always going to be a non negative integer), will return:

* attribute modifier, as indicated on the table of the above link;
* maximum spell level for the spells you can cast (-1 for no spells at all) with that score;
* the eventual extra spells you might get (as an array/list, with elements representing extra spells for 1st, 2nd,... spell level in order; empty array for no extra spells).

The result needs to be an object (associative array in PHP), as shown in the examples:

```python
char_attribute(0) == {"modifier": 0, "maximum_spell_level": -1, "extra_spells": []}
char_attribute(1) == {"modifier": -5, "maximum_spell_level": -1, "extra_spells": []}
char_attribute(5) == {"modifier": -3, "maximum_spell_level": -1, "extra_spells": []}
char_attribute(10) == {"modifier": 0, "maximum_spell_level": 0, "extra_spells": []}
char_attribute(20) == {"modifier": +5, "maximum_spell_level": 9, "extra_spells": [2,1,1,1,1]}
```

*Note: I didn't explain things in detail and just pointed out to the table on purpose, as my goal is also to train the pattern recognition skills of whoever is going to take this challenges, so do not complain about a summary description. Thanks :)*

In the same series:

* [D&D Character generator #1: attribute modifiers and spells](https://www.codewars.com/kata/d-and-d-character-generator-number-1-attribute-modifiers-and-spells/)
* [D&D Character generator #2: psion power points](https://www.codewars.com/kata/d-and-d-character-generator-number-2-psion-power-points/)
* [D&D Character generator #3: carrying capacity](https://www.codewars.com/kata/d-and-d-character-generator-number-3-carrying-capacity/)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded