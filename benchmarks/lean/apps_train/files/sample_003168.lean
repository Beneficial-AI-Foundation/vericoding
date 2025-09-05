## Task
You need to implement two functions, `xor` and `or`, that replicate the behaviour of their respective operators:

- `xor` = Takes 2 values and returns `true` if, and only if, one of them is truthy.
- `or` = Takes 2 values and returns `true` if either one of them is truthy.

When doing so, **you cannot use the or operator: `||`**.

# Input
- Not all input will be booleans - there will be truthy and falsey values [the latter including also empty strings and empty arrays]
- There will always be 2 values provided

## Examples
- `xor(true, true)` should return `false`
- `xor(false, true)` should return `true`
- `or(true, false)` should return `true`
- `or(false, false)` should return `false`

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded