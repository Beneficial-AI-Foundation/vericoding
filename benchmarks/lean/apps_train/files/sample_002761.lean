Following from the previous kata and taking into account how cool psionic powers are compare to the Vance spell system (really, the idea of slots to dumb down the game sucks, not to mention that D&D became a smash hit among geeks, so...), your task in this kata is to create a function that returns how many power points you get as a psion [because psions are the coolest, they allow for a lot of indepth tactic playing and adjusting for psychic warriors or wilders or other non-core classes would be just an obnoxious core].

Consider both [the psion power points/days table](http://www.dandwiki.com/wiki/SRD:Psion#Making_a_Psion) and [bonus power points](http://www.d20pfsrd.com/psionics-unleashed/classes/#Table_Ability_Modifiers_and_Bonus_Power_Points) to figure out the correct reply, returned as an integer; the usual interpretation is that bonus power points stop increasing after level 20, but for the scope of this kata, we will pretend they keep increasing as they did before.

To compute the total, you will be provided, both as non-negative integers:

* class level (assume they are all psion levels and remember the base power points/day halts after level 20)
* manifesting attribute score (Intelligence, to be more precise) to determine the total, provided the score is high enough for the character to manifest at least one power.

Some examples:

```python
psion_power_points(1,0) == 0
psion_power_points(1,10) == 0
psion_power_points(1,11) == 2
psion_power_points(1,20) == 4
psion_power_points(21,30) == 448
```

*Note: I didn't explain things in detail and just pointed out to the table on purpose, as my goal is also to train the pattern recognition skills of whoever is going to take this challenges, so do not complain about a summary description. Thanks :)*

In the same series:

* [D&D Character generator #1: attribute modifiers and spells](https://www.codewars.com/kata/d-and-d-character-generator-number-1-attribute-modifiers-and-spells/)
* [D&D Character generator #2: psion power points](https://www.codewars.com/kata/d-and-d-character-generator-number-2-psion-power-points/)
* [D&D Character generator #3: carrying capacity](https://www.codewars.com/kata/d-and-d-character-generator-number-3-carrying-capacity/)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible