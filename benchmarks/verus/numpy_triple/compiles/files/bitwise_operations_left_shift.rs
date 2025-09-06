/* Shift the bits of an integer to the left

Shift the bits of an integer to the left.

Bits are shifted to the left by appending x2 0s at the right of x1. Since the internal representation of numbers is in binary format, this operation is equivalent to multiplying x1 by 2**x2.

Parameters
----------
x1 : array_like of integer type
    Input values.
x2 : array_like of integer type
    Number of zeros to append to x1. Has to be non-negative.
    If x1.shape != x2.shape, they must be broadcastable to a common shape.
out : ndarray, None, or tuple of ndarray and None, optional
    A location into which the result is stored.
where : array_like, optional
    This condition is broadcast over the input.

Returns
-------
out : ndarray of integer type
    Return x1 with bits shifted x2 times to the left.
    This is a scalar if both x1 and x2 are scalars.

See Also
--------
right_shift : Shift the bits of an integer to the right.
binary_repr : Return the binary representation of the input number as a string.

Examples
--------
>>> np.left_shift(5, 2)
20
>>> np.left_shift(5, [1,2,3])
array([10, 20, 40])

Note that the dtype of the second argument may change the dtype of the result and can lead to unexpected results in some cases:

>>> a = np.left_shift(np.uint8(255), 1) # Expect 254
>>> print(a, type(a)) # Unexpected result due to upcasting
510 <class 'numpy.int64'>
>>> b = np.left_shift(np.uint8(255), np.uint8(1))
>>> print(b, type(b))
254 <class 'numpy.uint8'>

Shift the bits of integers to the left element-wise.
This operation is equivalent to multiplying each element by 2^shift_amount.

Specification: left_shift performs bitwise left shift operation on each element.
The result is equivalent to multiplying x1[i] by 2^x2[i] for non-negative shifts.

Mathematical properties:
1. Core behavior: Each element result[i] = x1[i] * 2^x2[i] for non-negative shifts
2. Identity property: Shifting by 0 returns the original value
3. Zero preservation: Shifting zero always yields zero
4. Monotonicity: For positive values, left shifting increases magnitude
5. Composition property: left_shift(x, a) then left_shift(result, b) = left_shift(x, a+b) */

use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
fn left_shift(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == x1[i] * pow(2, x2[i] as nat),
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == 0,
        forall|i: int| 0 <= i < result.len() && x1[i] > 0 && x2[i] > 0 ==> result[i] > x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] < 0 && x2[i] > 0 ==> result[i] < x1[i],
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}