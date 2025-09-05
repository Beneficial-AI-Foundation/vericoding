For all x in the range of integers [0, 2 ** n), let y[x] be the binary exclusive-or of x and x // 2. Find the sum of all numbers in y.

Write a function sum_them that, given n, will return the value of the above sum.

This can be implemented a simple loop as shown in the initial code. But once n starts getting to higher numbers, such as 2000 (which will be tested), the loop is too slow.

There is a simple solution that can quickly find the sum. Find it!

Assume that n is a nonnegative integer.

Hint: The complete solution can be written in two lines.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
