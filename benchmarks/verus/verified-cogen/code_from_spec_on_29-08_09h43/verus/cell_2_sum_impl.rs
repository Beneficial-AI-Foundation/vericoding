use vstd::prelude::*;

verus!{

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)
    // pre-conditions-start
    requires 
        old(a).len() == N,
        N <= 0x7FFF_FFFF,
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum <= 2*N,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    0
    // impl-end
}
// </vc-code>

}

fn main() {}