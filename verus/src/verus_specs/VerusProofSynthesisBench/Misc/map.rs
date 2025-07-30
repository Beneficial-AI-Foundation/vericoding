use vstd::prelude::*;

verus!{
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
{
    // TODO: Remove this comment and implement the function body
}
}

fn main() {}
