# Task

The game starts with `n` people standing in a circle. The presenter counts `m` people starting with the first one, and gives `1` coin to each of them. The rest of the players receive `2` coins each. After that, the last person who received `1` coin leaves the circle, giving everything he had to the next participant (who will also be considered "the first in the circle" in the next round). This process continues until only 1 person remains.

Determine the `number` of this person and how many `coins` he has at the end of the game.

The result should be a pair of values in the format: `[person, coins]`.

## Example:

```
n = 8, m = 3

People
1 2 3      1 2 ∙      1 2 ∙      ∙ 2 ∙       ∙  2 ∙       ∙ ∙  ∙       ∙ ∙  ∙
8   4  =>  8   4  =>  8   4  =>  8   4  =>   8    4  =>   8    4  =>   ∙    4  =>  7
7 6 5      7 6 5      7 ∙ 5      7 ∙ 5       7  ∙ ∙       7 ∙  ∙       7 ∙  ∙

Coins
0 0 0      1 1 ∙      3 3 ∙      ∙ 9 ∙       ∙ 10 ∙       ∙ ∙  ∙       ∙ ∙  ∙   
0   0  =>  2   3  =>  4   4  =>  5   6  =>   7    7  =>   8   20  =>   ∙   30  =>  51
0 0 0      2 2 2      7 ∙ 3      8 ∙ 5      16 ∙  ∙      17 ∙  ∙      18 ∙  ∙ 
```

## Notes:

* The presenter can do several full circles during one counting.
* In this case, the same person will receive `1` coin multiple times, i.e. no matter how many people are left in the circle, at least `m` coins will always be distributed among the participants during the round.
* If a person had already received `1` coin (possibly multiple times), he won't receive any additional `2` coins **at once(!)** during that round.
* People are counted starting with `1`.
* `m` can be **bigger** than `n` at start

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
