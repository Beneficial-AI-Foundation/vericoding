We have a set of consecutive numbers from ```1``` to ```n```.
We want to count all the subsets that do not contain consecutive numbers.
E.g.

If our set ```S1``` is equal to ```[1,2,3,4,5]```
The subsets that fulfill these property are:
```
[1],[2],[3],[4],[5],[1,3],[1,4],[1,5],[2,4],[2,5],[3,5],[1,3,5]
```
A total of      ```12   ``` subsets.

From the set ```S2``` equals to```[1,2,3]```, it is obvious that we have only ```4``` subsets and are:
```
[1],[2],[3],[1,3]
```
Make a code that may give the amount of all these subsets for any integer       ```n >= 2       ```.

Features of the random tests:
```
number of tests = 100 
10 <= n <= 120
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible