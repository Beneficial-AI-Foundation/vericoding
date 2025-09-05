## Find Mean

Find the mean (average) of a list of numbers in an array.

## Information

To find the mean (average) of a set of numbers add all of the numbers together and divide by the number of values in the list.

For an example list of `1, 3, 5, 7`

1. Add all of the numbers

```
1+3+5+7 = 16
```

2. Divide by the number of values in the list. In this example there are 4 numbers in the list.

```
16/4 = 4
```

3. The mean (or average) of this list is 4

def find_average [Add α] [Div α] [OfNat α 0] : List α → α 
  | [] => 0
  | xs => sorry

def list_min : List Float → Float 
  | [] => 0
  | (x::xs) => sorry

def list_max : List Float → Float
  | [] => 0
  | (x::xs) => sorry

def list_sum : List Float → Float
  | [] => 0
  | (x::xs) => sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
