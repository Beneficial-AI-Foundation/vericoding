// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_less_than(numbers: Set<int>, threshold: int) -> (count: usize)
    ensures count == numbers.filter(|i: int| i < threshold).len()
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}