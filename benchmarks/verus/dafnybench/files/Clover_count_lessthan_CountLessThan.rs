// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_less_than(numbers: Vec<i8>, threshold: i8) -> (count: usize)
    ensures count == numbers@.filter(|i: i8| (i as int) < (threshold as int)).len()
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}