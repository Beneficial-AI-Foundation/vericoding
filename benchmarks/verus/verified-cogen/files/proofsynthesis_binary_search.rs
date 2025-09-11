// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn binary_search(v: &Vec<u64>, k: u64) -> (result:usize)

    requires
        forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i:int| 0 <= i < v.len() && k == v[i],

    ensures
        result < v.len(),
        k == v[result as int],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}