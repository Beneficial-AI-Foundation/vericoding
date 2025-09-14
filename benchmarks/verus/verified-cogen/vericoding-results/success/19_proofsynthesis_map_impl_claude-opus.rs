// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun2(x: &mut Vec<i32>) 

    requires 
        forall |k:int| 0 <= k < old(x).len() ==> old(x)[k] <= 0x7FFF_FFFB,

    ensures 
        x@.len() == old(x)@.len(),
        forall |k:int| 0 <= k < x.len() ==> #[trigger] x@[k] == old(x)@[k] + 4,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): add decreases clause to fix loop verification */
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            x@.len() == old(x)@.len(),
            forall |k: int| 0 <= k < i ==> x@[k] == old(x)@[k] + 4,
            forall |k: int| i <= k < x.len() ==> x@[k] == old(x)@[k],
            forall |k: int| 0 <= k < x.len() ==> old(x)[k] <= 0x7FFF_FFFB,
        decreases x.len() - i
    {
        let val = x[i];
        x.set(i, val + 4);
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}