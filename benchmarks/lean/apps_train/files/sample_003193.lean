~~~if:csharp,javascript,cfml,php
Given a 2D array of size `m * n`. Your task is to find the sum of minimum value in each row.
~~~
~~~if:cpp
Given a 2D vector of size `m * n`. Your task is to find the sum of minimum value in each row.
~~~
~~~if:python,ruby
Given a 2D list of size `m * n`. Your task is to find the sum of minimum value in each row.
~~~

For Example:
```python
[
  [1, 2, 3, 4, 5],       # minimum value of row is 1
  [5, 6, 7, 8, 9],       # minimum value of row is 5
  [20, 21, 34, 56, 100]  # minimum value of row is 20
]
```
So, the function should return `26` because sum of minimums is as `1 + 5 + 20 = 26`

~~~if:javascript,php
Note: You will be always given non-empty array containing Positive values.
~~~
~~~if:python
Note: You will be always given non-empty list containing Positive values.
~~~
~~~if:cpp
Note: You will be always given non-empty vector containing Positive values.
~~~
~~~if:c#
Note: You will be always given non-empty vector containing Positive values.
~~~
~~~if:cfml
Note: You will be always given non-empty array containing Positive values.
~~~

ENJOY CODING :)

def List.minimums (l : List (List Int)) : Int := sorry 

def List.sum (l : List Int) : Int := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded