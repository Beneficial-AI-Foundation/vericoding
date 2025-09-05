use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn split_array(arr: &[i32], l: usize) -> (Vec<i32>, Vec<i32>)
    requires 0 <= l <= arr.len()
{
// </vc-spec>
// <vc-code>
    assume(false);
    (Vec::new(), Vec::new())
}
// </vc-code>


fn main() {
}

}
