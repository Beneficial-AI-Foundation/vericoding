// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_identical_positions(a: Vec<i8>, b: Vec<i8>, c: Vec<i8>) -> (count: usize)
    requires
        a.len() == b.len() && b.len() == c.len(),
    ensures
        count >= 0,
        count == Set::<int>::new(|i: int| 0 <= i < a@.len() && a@[i] == b@[i] && b@[i] == c@[i]).len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}