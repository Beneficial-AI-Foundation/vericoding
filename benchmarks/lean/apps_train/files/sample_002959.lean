There are some candies that need to be distributed to some children as fairly as possible (i.e. the variance of result needs to be as small as possible), but I don't know how to distribute them, so I need your help. Your assignment is to write a function with signature `distribute(m, n)` in which `m` represents how many candies there are, while `n` represents how many children there are. The function should return a container which includes the number of candies each child gains.

# Notice
1. *The candy can't be divided into pieces.*
2. The list's order doesn't matter.

# Requirements
1. The case `m < 0` is equivalent to `m == 0`.
2. If `n <= 0` the function should return an empty container. 
3. If there isn't enough candy to distribute, you should fill the corresponding number with `0`.

# Examples
```python
distribute(-5,  0) # should be [] 
distribute( 0,  0) # should be [] 
distribute( 5,  0) # should be [] 
distribute(10,  0) # should be [] 
distribute(15,  0) # should be [] 
distribute(-5, -5) # should be [] 
distribute( 0, -5) # should be [] 
distribute( 5, -5) # should be [] 
distribute(10, -5) # should be [] 
distribute(15, -5) # should be []
distribute(-5, 10) # should be [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
distribute( 0, 10) # should be [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
distribute( 5, 10) # should be [1, 1, 1, 1, 1, 0, 0, 0, 0, 0]
distribute(10, 10) # should be [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
distribute(15, 10) # should be [2, 2, 2, 2, 2, 1, 1, 1, 1, 1]
```

# Input
  1. m: Integer (m <= 100000)
  2. n: Integer (n <= 1000)

# Output
  1. [Integer]

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
