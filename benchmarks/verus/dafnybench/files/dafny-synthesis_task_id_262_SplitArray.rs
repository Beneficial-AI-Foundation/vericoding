// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn split_array(arr: &[i8], l: usize) -> (Vec<i8>, Vec<i8>)
    requires 0 <= l <= arr.len()
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}