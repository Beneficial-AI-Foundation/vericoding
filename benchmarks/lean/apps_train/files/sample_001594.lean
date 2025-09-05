This kata is a continuation of [Part 1](http://www.codewars.com/kata/the-fibfusc-function-part-1). The `fibfusc` function is defined recursively as follows:

    fibfusc(0) = (1, 0)
    fibfusc(1) = (0, 1)
    fibfusc(2n) = ((x + y)(x - y), y(2x + 3y)), where (x, y) = fibfusc(n)
    fibfusc(2n + 1) = (-y(2x + 3y), (x + 2y)(x + 4y)), where (x, y) = fibfusc(n)

Your job is to produce the code for the `fibfusc` function. In this kata, your function will be tested with large values of n (up to 2000 bits), so you should be concerned about stack overflow and timeouts. Moreover, since the `fibfusc` function grows exponentially, your function should take an extra argument `num_digits` with a default value of `None`. When not `None`, `num_digits` takes a positive `int` value and the returned values shall be truncated to the last `num_digits` digits. 

For example, let `n = 101`. With `num_digits` not set or set to `None`, `fibfusc` should return: 
`(-280571172992510140037611932413038677189525L, 734544867157818093234908902110449296423351L)`. If `num_digits = 12`, the function should return `(-38677189525L, 449296423351L)`. Notice in particular, that for any value of `n` greater than 1, `x` is negative, and the truncated value of `x` should also be negative.

Hint 1: Use modulo `10 ** num_digits` arithmetic to keep all intermediary results small.

Hint 2: Consider using an iterative ["number climber"](http://www.codewars.com/kata/number-climber) to avoid stack overflows.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded