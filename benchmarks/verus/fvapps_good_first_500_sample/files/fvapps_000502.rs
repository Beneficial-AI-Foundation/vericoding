// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_longest_increasing_paths(n: usize, values: Vec<usize>, edges: Vec<(usize, usize)>) -> (result: Vec<usize>)
    requires 
        n >= 2,
        values.len() == n,
        edges.len() == n - 1,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 1,
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