/* IEEE 754 floating point representation of negative zero.

Specification: NZERO represents IEEE 754 negative zero, which equals zero 
but has special properties in floating point arithmetic */

use vstd::prelude::*;

verus! {
fn nzero() -> (result: f32)
    ensures
        result == 0.0f32,
        result + 0.0f32 == 0.0f32,
        result - 0.0f32 == 0.0f32,
        result * 1.0f32 == 0.0f32,
        result * 2.0f32 == 0.0f32,
        result / 1.0f32 == 0.0f32,
        result + 1.0f32 == 1.0f32,
        result + (-1.0f32) == -1.0f32,
        1.0f32 - result == 1.0f32,
        (-1.0f32) - result == -1.0f32,
        result.abs() == 0.0f32,
{
    // impl-start
    assume(false);
    0.0f32
    // impl-end
}
}
fn main() {}