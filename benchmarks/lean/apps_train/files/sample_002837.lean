A `bouncy number` is a positive integer whose digits neither increase nor decrease. For example, 1235 is an increasing number, 5321 is a decreasing number, and 2351 is a bouncy number. By definition, all numbers under 100 are non-bouncy, and 101 is the first bouncy number.

Determining if a number is bouncy is easy, but counting all bouncy numbers with N digits can be challenging for large values of N. To complete this kata, you must write a function that takes a number N and return the count of bouncy numbers with N digits. For example, a "4 digit" number includes zero-padded, smaller numbers, such as 0001, 0002, up to 9999.

For clarification, the bouncy numbers between 100 and 125 are: 101, 102, 103, 104, 105, 106, 107, 108, 109, 120, and 121.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded