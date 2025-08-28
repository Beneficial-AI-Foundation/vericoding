use vstd::prelude::*;

verus!{

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn myfun2(x: &mut Vec<i32>) 
    // pre-conditions-start
    requires 
        forall |k:int| 0 <= k < old(x).len() ==> old(x)[k] <= 0x7FFF_FFFB,
    // pre-conditions-end
    // post-conditions-start
    ensures 
        x@.len() == old(x)@.len(),
        forall |k:int| 0 <= k < x.len() ==> #[trigger] x@[k] == old(x)@[k] + 4,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            x@.len() == old(x)@.len(),
            forall |k:int| 0 <= k < i ==> #[trigger] x@[k] == old(x)@[k] + 4,
            forall |k:int| i <= k < x.len() ==> #[trigger] x@[k] == old(x)@[k],
            forall |k:int| 0 <= k < old(x).len() ==> old(x)[k] <= 0x7FFF_FFFB,
        decreases x.len() - i
    {
        x[i] = x[i] + 4;
        i = i + 1;
    }
    // impl-end
}
// </vc-code>

}

fn main() {}