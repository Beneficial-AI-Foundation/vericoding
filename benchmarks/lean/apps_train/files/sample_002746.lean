Ho ho! So you think you know integers, do you? Well then, young wizard, tell us what the Nth digit of the [Champernowne constant](https://en.wikipedia.org/wiki/Champernowne_constant) is!

The constant proceeds like this: `0.12345678910111213141516...`

I hope you see the pattern!

Conjure a function that will accept an integer, `n`, and return the (one-indexed) `n`th digit of Champernowne's constant. Can you get it to run in _constant_ time?

For example:

`n = 1` should return `0` (the very first digit)

`n = 2` should return `1` (we ignore the period character since it's not a digit!)

`n = 20` should return `4` (that's the `4` in the number `14`, 20th in sequence)

For any invalid values, such as `0` and below, or non-integers, return... `NaN`!

I hope (for your sake) that you've been practicing your mathemagical spells, because a naïve solution will _not_ be fast enough to compete in this championship!

Invoke with _precision_, and be wary of rounding errors in the realms of enormity!

May the best integer win!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
