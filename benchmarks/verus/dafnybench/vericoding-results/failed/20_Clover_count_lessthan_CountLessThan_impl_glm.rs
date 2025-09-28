use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn make_less_than(threshold: int) -> spec_fn(int) -> bool
    recommends forall |i: int| make_less_than(threshold)(i) == (i < threshold)
{
    |i: int| i < threshold
}
// </vc-helpers>

// <vc-spec>
fn count_less_than(numbers: Set<int>, threshold: int) -> (count: usize)
    ensures count == numbers.filter(|i: int| i < threshold).len()
// </vc-spec>
// <vc-code>
{
    let count = numbers.filter(|i: int| i < threshold).len();
    count as usize
}
// </vc-code>

fn main() {}

}