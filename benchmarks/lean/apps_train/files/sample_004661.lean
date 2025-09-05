# Story

Old MacDingle had a farm... 

...and on that farm he had

* horses 
* chickens 
* rabbits 
* some apple trees
* a vegetable patch

Everything is idylic in the MacDingle farmyard **unless somebody leaves the gates open**

Depending which gate was left open then...

* horses might run away
* horses might eat the apples
* horses might eat the vegetables
* chickens might run away
* rabbits might run away
* rabbits might eat the vegetables

# Kata Task

Given the state of the farm gates in the evening, your code must return what the farm looks like the next morning when daylight reveals what the animals got up to.

# Legend

* ```H``` horse
* ```C``` chicken
* ```R``` rabbit
* ```A``` apple tree
* ```V``` vegetables
* ```|``` gate (closed), 
* ```\``` or ```/``` gate (open)
* ```.``` everything else

# Example

Before
```|..HH....\AAAA\CC..|AAA/VVV/RRRR|CCC```

After
```|..HH....\....\CC..|AAA/.../RRRR|...```
Because:

The horses ate whatever apples they could get to
The rabbits ate the vegetables
The chickens ran away

# Notes

* If the animals can eat things *and* also run away then they do **BOTH** - it is best not to run away when you are hungry!
* An animal cannot "go around" a closed gate...
* ...but it is possible to run away from the farm and then **RUN BACK** and re-enter though more open gates on the other side!

def split_on_char (c : Char) (s : List Char) : List (List Char) :=
  sorry

def any (p : Char → Bool) (s : List Char) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded