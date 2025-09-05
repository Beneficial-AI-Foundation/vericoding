You are given a certain integer, ```n, n > 0```. You have to search the partition or partitions, of n, with maximum product value.

Let'see the case for ```n = 8```.
```
Partition                 Product
[8]                          8
[7, 1]                       7
[6, 2]                      12
[6, 1, 1]                    6
[5, 3]                      15
[5, 2, 1]                   10
[5, 1, 1, 1]                 5
[4, 4]                      16
[4, 3, 1]                   12
[4, 2, 2]                   16
[4, 2, 1, 1]                 8
[4, 1, 1, 1, 1]              4
[3, 3, 2]                   18   <---- partition with maximum product value
[3, 3, 1, 1]                 9
[3, 2, 2, 1]                12
[3, 2, 1, 1, 1]              6
[3, 1, 1, 1, 1, 1]           3
[2, 2, 2, 2]                16
[2, 2, 2, 1, 1]              8
[2, 2, 1, 1, 1, 1]           4
[2, 1, 1, 1, 1, 1, 1]        2
[1, 1, 1, 1, 1, 1, 1, 1]     1
```
So our needed function will work in that way for Python and Ruby:
```
find_part_max_prod(8) == [[3, 3, 2], 18]
```
For javascript
```
findPartMaxProd(8) --> [[3, 3, 2], 18]
```
If there are more than one partition with maximum product value, the function should output the patitions in a length sorted way.
Python and Ruby
```
find_part_max_prod(10) == [[4, 3, 3], [3, 3, 2, 2], 36]
```
Javascript
```
findPartMaxProd(10) --> [[4, 3, 3], [3, 3, 2, 2], 36]
```
Enjoy it!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
