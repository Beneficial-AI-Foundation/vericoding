We have an integer array with unique elements and we want to do the permutations that have an element fixed, in other words, these permutations should have a certain element at the same position than the original.

These permutations will be called: **permutations with one fixed point**.

Let's see an example with an array of four elements and we want the permutations that have a coincidence **only at  index 0**, so these permutations are (the permutations between parenthesis):
``` 
arr = [1, 2, 3, 4]
      (1, 3, 4, 2)
      (1, 4, 2, 3)
Two permutations matching with arr only at index 0
``` 

Let's see the permutations of the same array with only one coincidence at index **1**:
``` 
arr = [1, 2, 3, 4]
      (3, 2, 4, 1)
      (4, 2, 1, 3)
Two permutations matching with arr only at index 1
```
Once again, let's see the permutations of the same array with only one coincidence at index **2**:
``` 
arr = [1, 2, 3, 4]
      (2, 4, 3, 1)
      (4, 1, 3, 2)
Two permutations matching with arr only at index 2
```
Finally, let's see the permutations of the same array with only one coincidence at index **3**:
``` 
arr = [1, 2, 3, 4]
      (2, 3, 1, 4)
      (3, 1, 2, 4)
Two permutations matching with arr only at index 3
```
For this array given above (arr) :

- We conclude that we have 8 permutations with one fixed point (two at each index of arr).

- We may do the same development for our array, `arr`, with two fixed points and we will get `6` permutations.

- There are no permutations with coincidences only at three indexes.

- It's good to know that the amount of permutations with no coincidences at all are `9`. See the kata Shuffle It Up!!

In general:

- When the amount of fixed points is equal to the array length, there is only one permutation, the original array.

- When the amount of fixed points surpasses the length of the array, obvously, there are no permutations at all.

Create a function that receives the length of the array and the number of fixed points and may output the total amount of permutations for these constraints.

Features of the random tests:
```
length of the array = l
number of fixed points = k
10 ≤ k ≤ l ≤ 9000
```
See the example tests!
Enjoy it!!

Ruby versin will be released soon.

#Note: This kata was published previously but in a version not well optimized.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible