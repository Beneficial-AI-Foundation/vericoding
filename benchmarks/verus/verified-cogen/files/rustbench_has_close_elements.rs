// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_spec(i: int) -> int {
    if i < 0 { -i } else { i }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn has_close_elements(numbers: &[i32], threshold: i32) -> (flag: bool)
    requires
        threshold > 0,
        forall|i: int, j: int| 0 <= i && i < numbers.len() && 0 <= j && j < numbers.len() ==> numbers[i] - numbers[j] < i32::MAX && -(numbers[i] - numbers[j]) < i32::MAX
    ensures
        flag == exists|i: int, j: int| 0 <= i && 0 <= j && i < numbers.len() && j < numbers.len() && i != j && abs_spec(numbers[i] - numbers[j]) < threshold
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}