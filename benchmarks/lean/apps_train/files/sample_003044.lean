Implement `String#parse_mana_cost`, which parses [Magic: the Gathering mana costs](http://mtgsalvation.gamepedia.com/Mana_cost) expressed as a string and returns a `Hash` with keys being kinds of mana, and values being the numbers.

Don't include any mana types equal to zero.

Format is:

* optionally natural number representing total amount of generic mana (use key `*`)
* optionally followed by any combination of `w`, `u`, `b`, `r`, `g` (case insensitive in input, return lower case in output), each representing one mana of specific color.

If case of Strings not following specified format, return `nil/null/None`.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded