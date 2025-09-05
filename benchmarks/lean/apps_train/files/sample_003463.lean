Assume we take a number `x` and perform any one of the following operations:
```Pearl
a) Divide x by 3 (if it is divisible by 3), or
b) Multiply x by 2
```
After each operation, we write down the result. If we start with `9`, we can get a sequence such as:
```
[9,3,6,12,4,8] -- 9/3=3 -> 3*2=6 -> 6*2=12 -> 12/3=4 -> 4*2=8
```
You will be given a shuffled sequence of integers and your task is to reorder them so that they conform to the above sequence. There will always be an answer. 
```
For the above example:
solve([12,3,9,4,6,8]) = [9,3,6,12,4,8].
```

More examples in the test cases. Good luck!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded