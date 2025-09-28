// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_linalg_cross(x1: [i8; 3], x2: [i8; 3]) -> (result: [i8; 3])
    ensures
        result[0] as int == x1[1] as int * x2[2] as int - x1[2] as int * x2[1] as int,
        result[1] as int == x1[2] as int * x2[0] as int - x1[0] as int * x2[2] as int,
        result[2] as int == x1[0] as int * x2[1] as int - x1[1] as int * x2[0] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use int to avoid overflow and assert range for cast */
    let r0 = x1[1] as int * x2[2] as int - x1[2] as int * x2[1] as int;
    let r1 = x1[2] as int * x2[0] as int - x1[0] as int * x2[2] as int;
    let r2 = x1[0] as int * x2[1] as int - x1[1] as int * x2[0] as int;

    // The ensures clause implies the result must fit in an i8.
    // This is only possible if the inputs satisfy a precondition that the
    // cross product computations do not exceed the i8 range.
    // Since this precondition is missing from the spec, we assert it here.
    // Verus will correctly fail to prove this assertion for arbitrary inputs.
    assert(i8::MIN as int <= r0 && r0 <= i8::MAX as int);
    assert(i8::MIN as int <= r1 && r1 <= i8::MAX as int);
    assert(i8::MIN as int <= r2 && r2 <= i8::MAX as int);

    let result = [r0 as i8, r1 as i8, r2 as i8];
    result
}
// </vc-code>


}
fn main() {}