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
    /* code modified by LLM (iteration 2): added invariant to prove absence of overflow */
    let mut i: usize = 0;
    while i < x.len()
        invariant
            x.len() == old(x).len(),
            forall |k:int| 0 <= k < old(x).len() ==> old(x)[k] <= 0x7FFF_FFFB,
            forall|j: int| 0 <= j < i ==> x@[j] == old(x)@[j] + 4,
            forall|j: int| i <= j < x.len() ==> x@[j] == old(x)@[j],
        decreases x.len() - i
    {
        x[i] = x[i] + 4;
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}