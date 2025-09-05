[Generala](https://en.wikipedia.org/wiki/Generala) is a dice game popular in South America. It's very similar to [Yahtzee](https://en.wikipedia.org/wiki/Yahtzee) but with a different scoring approach. It is played with 5 dice, and the possible results are:

| Result        | Points | Rules                                                                                                                                          | Samples                            |
|---------------|--------|------------------------------------------------------------------------------------------------------------------------------------------------|------------------------------------|
| GENERALA      | 50     | When all rolled dice are of the same value.                                                                                                    | 66666, 55555, 44444, 11111, 22222, 33333.  |
| POKER         | 40     | Four rolled dice are of the same value.                                                                                                        | 44441, 33233, 22262.               |
| FULLHOUSE     | 30     | Three rolled dice are of the same value, the remaining two are of a different value, but equal among themselves.                               | 12121, 44455, 66116.               |
| STRAIGHT      | 20     | Rolled dice are in sequential order. Dice with value `1` is a wildcard that can be used at the beginning of the straight, or at the end of it. | 12345, 23456, 34561, 13654, 62534. |
| Anything else | 0      | Anything else will return `0` points.                                                                                                          | 44421, 61623, 12346.               |

Please note that dice are not in order; for example `12543` qualifies as a `STRAIGHT`. Also, No matter what string value you get for the dice, you can always reorder them any order you need to make them qualify as a `STRAIGHT`. I.E. `12453`, `16543`, `15364`, `62345` all qualify as valid `STRAIGHT`s.

Complete the function that is given the rolled dice as a string of length `5` and return the points scored in that roll. You can safely assume that provided parameters will be valid:

 * String of length 5,
 * Each character will be a number between `1` and `6`

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded