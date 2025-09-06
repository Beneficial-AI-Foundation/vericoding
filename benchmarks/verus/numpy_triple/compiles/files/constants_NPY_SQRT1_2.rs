/* 
{
  "name": "NPY_SQRT1_2",
  "category": "C API Mathematical constants",
  "description": "Square root of 1/2",
  "doc": "√(1/2) = 0.707106781186547524400844362104849039",
}
*/

/* NPY_SQRT1_2: Square root of 1/2 as a Float constant */

/* Specification: NPY_SQRT1_2 equals the square root of 1/2 with mathematical properties */
use vstd::prelude::*;

verus! {
// <vc-helpers>
// </vc-helpers>
fn NPY_SQRT1_2() -> (result: f64)
// <vc-implementation>
{
    return 0.707106781186547524400844362104849039; // TODO: Remove this line and implement the function body
}
// </vc-implementation>
proof fn NPY_SQRT1_2_spec()
    /* ensures result * result == 0.5 && 
              result > 0.0 &&
              result == (0.5 as f64).sqrt() &&
              result == 1.0 / (2.0 as f64).sqrt() &&
              (result - 0.707106781186547524400844362104849039).abs() < 1e-15 */
// <vc-proof>
{
    assume(false); // TODO: Remove this line and implement the proof
}
// </vc-proof>
fn main() {}

}