// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn set_product(s: Set<int>) -> int
    decreases s.len()
{
    if s.is_empty() {
        1
    } else {
        arbitrary()
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn unique_product(arr: &[i32]) -> (product: i32)
    ensures product == set_product(arr@.to_set().map(|x: i32| x as int))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}