// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x < 0 { -x } else { x }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: Seq<int>, threshold: int) -> (result: bool)
    ensures
        result <==> exists|i: int, j: int|
            0 <= i < numbers.len() &&
            0 <= j < numbers.len() &&
            i != j &&
            abs(numbers[i] - numbers[j]) < threshold,
        result ==> numbers.len() > 1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}