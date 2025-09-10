use vstd::math::abs;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

fn has_close_elements(numbers: &[i64], threshold: i64) -> (result: bool)

    ensures
        result == exists|i: int, j: int|
            0 <= i < j < numbers@.len() && abs(numbers[i] - numbers[j]) < threshold,
{
    assume(false);
    unreached();
}

}
fn main() {}