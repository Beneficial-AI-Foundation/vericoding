# Task

Given a binary number, we are about to do some operations on the number. Two types of operations can be here:

* ['I', i, j] : Which means invert the bit from i to j (inclusive).

* ['Q', i] : Answer whether the i'th bit is 0 or 1.

The MSB (most significant bit) is the first bit (i.e. i = `1`). The binary number can contain leading zeroes.

## Example
```python
binary_simulation("0011001100", [['I', 1, 10], ['I', 2, 7], ['Q', 2], ['Q', 1], ['Q', 7], ['Q', 5]]) === [ '0', '1', '1', '0' ];
binary_simulation("1011110111", [['I', 1, 10], ['I', 2, 7], ['Q', 2], ['Q', 1], ['Q', 7], ['Q', 5]]) === [ '0', '0', '0', '1' ];
binary_simulation("1011110111", [['I', 1, 10], ['I', 2, 7]]) === [];
binary_simulation("0000000000", [['I', 1, 10], ['Q', 2]]) ===  ['1'];
```
## Note
* All inputs are valid.
* Please optimize your algorithm to avoid time out.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded