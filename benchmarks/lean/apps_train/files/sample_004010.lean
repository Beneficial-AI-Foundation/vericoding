Variation of this nice kata, the war has expanded and become dirtier and meaner; both even and odd numbers will fight with their pointy `1`s. And negative integers are coming into play as well, with, ça va sans dire, a negative contribution (think of them as spies or saboteurs).

Again, three possible outcomes: `odds win`, `evens win` and `tie`.

Examples:

```python
bits_war([1,5,12]) => "odds win" #1+101 vs 1100, 3 vs 2
bits_war([7,-3,20]) => "evens win" #111-11 vs 10100, 3-2 vs 2
bits_war([7,-3,-2,6]) => "tie" #111-11 vs -1+110, 3-2 vs -1+2
```

def bits_war (numbers : List Int) : String := sorry

def bitsToCount (n : Int) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
