Here's a way to construct a list containing every positive rational number:

Build a binary tree where each node is a rational and the root is `1/1`, with the following rules for creating the nodes below:
* The value of the left-hand node below `a/b` is `a/a+b`
* The value of the right-hand node below `a/b` is `a+b/b`

So the tree will look like this:

```
                       1/1
                  /           \ 
            1/2                  2/1
           /    \              /     \
       1/3        3/2        2/3       3/1
      /   \      /   \      /   \     /   \
   1/4    4/3  3/5   5/2  2/5   5/3  3/4   4/1

 ...
```

Now traverse the tree, breadth first, to get a list of rationals.

```
[ 1/1, 1/2, 2/1, 1/3, 3/2, 2/3, 3/1, 1/4, 4/3, 3/5, 5/2, .. ]
```

Every positive rational will occur, in its reduced form, exactly once in the list, at a finite index.

```if:haskell
In the kata, we will use tuples of type `(Integer, Integer)` to represent rationals, where `(a, b)` represents `a / b`
```
```if:javascript
In the kata, we will use tuples of type `[ Number, Number ]` to represent rationals, where `[a,b]` represents `a / b`
```

Using this method you could create an infinite list of tuples:

matching the list described above:

However, constructing the actual list is too slow for our purposes. Instead, study the tree above, and write two functions:

For example:

def gcd (x y : Nat) : Nat :=
  sorry

def coprime (x y : Nat) : Prop :=
  gcd x y = 1

def rat_at (n : Nat) : Nat × Nat := 
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
