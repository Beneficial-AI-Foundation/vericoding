/* 
{
  "name": "numpy.False_",
  "category": "Boolean constants",
  "description": "NumPy boolean scalar representing False",
  "url": "https://numpy.org/doc/stable/reference/arrays.scalars.html",
  "doc": "NumPy's boolean type. Character code: '?'. Alias for numpy.bool_.\n\nComparison operations in NumPy return numpy.True_ or numpy.False_ instead of Python's built-in True or False.",
}
*/

/* NumPy's boolean False value, used in comparison operations and boolean arrays */

/* Specification: False_ represents the boolean false value with properties:
   1. It equals false
   2. It is the identity for logical OR
   3. It is the absorbing element for logical AND
   4. It is the negation of True_ */
use vstd::prelude::*;

verus! {
// <vc-helpers>
// </vc-helpers>
fn False_() -> (result: bool)
    ensures 
        result == false &&
        result == !true
{
    // <vc-implementation>
    return false; // TODO: Remove this line and implement the function body
    // </vc-implementation>
}
proof fn False__spec() {
// <vc-proof>
assume(false); // TODO: Remove this line and implement the proof
// </vc-proof>
}

fn main() {}

}