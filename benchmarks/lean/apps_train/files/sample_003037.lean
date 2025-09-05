Triangular numbers count the number of objects that can form an equilateral triangle. The nth triangular number forms an equilateral triangle with n dots on each side (including the vertices).
Here is a graphic example for the triangular numbers of 1 to 5:
```
n=1: triangular number: 1
*

n=2: triangular number: 3
 *
* *

n=3: triangular number: 6
  *
 * *
* * *

n=4: triangular number: 10
    *
   * *
  * * *
 * * * *

 n=5: triangular number: 15
      *
     * *
    * * *
   * * * *
  * * * * *
```

Your task is to implement a function ```triangular_range(start, stop)``` that returns a dictionary of all numbers as keys and the belonging triangular numbers as values, where the triangular number is in the range start, stop (including start and stop).
For example, ```triangular_range(1, 3)``` should return ```{1: 1, 2: 3}``` and ```triangular_range(5, 16)``` should return ```{3: 6, 4: 10, 5: 15}```.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
