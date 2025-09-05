When you want to get the square of a binomial of two variables x and y, you will have:

`$(x+y)^2 = x^2 + 2xy + y ^2$`

And the cube:

`$(x+y)^3 = x^3 + 3x^2y + 3xy^2 +y^3$`

It is known from many centuries ago that for an exponent n, the result of a binomial x + y raised to the n-th power is:

Or using the sumation notation:

Each coefficient of a term has the following value:

Each coefficient value coincides with the amount of combinations without replacements of a set of n elements using only k different ones of that set.

Let's see the total sum of the coefficients of the different powers for the binomial:

`$(x+y)^0(1)$`

`$(x+y)^1 = x+y(2)$`

`$(x+y)^2 = x^2 + 2xy + y ^2(4)$`

`$(x+y)^3 = x^3 + 3x^2y + 3xy^2 +y^3(8)$`

We need a function that may generate an array with the values of all the coefficients sums from 0 to the value of n included and has the addition of all the sum values as last element.

We add some examples below:
``` 
f(0) = [1, 1]
f(1) = [1, 2, 3]
f(2) = [1, 2, 4, 7]
f(3) = [1, 2, 4, 8, 15]
``` 

Features of the test
``` 
Low Performance Tests
Number of tests = 50
9 < n < 101

High Performance Tests
Number of Tests = 50
99 < n < 5001
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
