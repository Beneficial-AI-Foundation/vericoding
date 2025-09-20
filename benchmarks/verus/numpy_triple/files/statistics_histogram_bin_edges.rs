// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn histogram_bin_edges(data: Vec<i8>, num_bins: usize) -> (edges: Vec<i8>)
    requires 
        data.len() > 0,
        num_bins > 0,
    ensures
        edges.len() == num_bins + 1,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}