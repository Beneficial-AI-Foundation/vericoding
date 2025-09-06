/* numpy.cross: Return the cross product of two (arrays of) vectors.

The cross product of a and b in R^3 is a vector perpendicular to both a and b.
For 3D vectors a = [a0, a1, a2] and b = [b0, b1, b2], the cross product is:
c = [a1*b2 - a2*b1, a2*b0 - a0*b2, a0*b1 - a1*b0]

This implementation focuses on the 3D case, which is the most common usage.
The result vector is perpendicular to both input vectors according to the
right-hand rule.

Specification: numpy.cross returns the cross product of two 3D vectors.

Precondition: True (vectors must be 3D, enforced by type)
Postcondition: 
1. The result components follow the cross product formula
2. The result is perpendicular to both input vectors (dot product is zero)
3. Anti-commutativity: a × b = -(b × a)
4. Bilinearity properties
5. Zero property: if a and b are parallel, then a × b = 0 */

use vstd::prelude::*;

verus! {
spec fn cross_product_spec(a: [i32; 3], b: [i32; 3]) -> [int; 3] {
    [
        (a[1] as int) * (b[2] as int) - (a[2] as int) * (b[1] as int),
        (a[2] as int) * (b[0] as int) - (a[0] as int) * (b[2] as int), 
        (a[0] as int) * (b[1] as int) - (a[1] as int) * (b[0] as int)
    ]
}

spec fn dot_product(x: [int; 3], y: [i32; 3]) -> int {
    x[0] * (y[0] as int) + x[1] * (y[1] as int) + x[2] * (y[2] as int)
}
fn cross(a: [i32; 3], b: [i32; 3]) -> (result: [i32; 3])
    ensures
        (result[0] as int) == (a[1] as int) * (b[2] as int) - (a[2] as int) * (b[1] as int),
        (result[1] as int) == (a[2] as int) * (b[0] as int) - (a[0] as int) * (b[2] as int), 
        (result[2] as int) == (a[0] as int) * (b[1] as int) - (a[1] as int) * (b[0] as int),
        dot_product(cross_product_spec(a, b), a) == 0,
        dot_product(cross_product_spec(a, b), b) == 0,
{
    // impl-start
    assume(false);
    [0, 0, 0]
    // impl-end
}
}
fn main() {}