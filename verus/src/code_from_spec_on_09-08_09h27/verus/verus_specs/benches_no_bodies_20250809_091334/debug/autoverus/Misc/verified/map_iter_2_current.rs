use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun2(x: &mut Vec<i32>) 
requires 
    forall |k:int| 0 <= k < old(x).len() ==> old(x)[k] <= 0x7FFF_FFFB,
ensures 
    x@.len() == old(x)@.len(),
    forall |k:int| 0 <= k < x.len() ==> #[trigger] x@[k] == old(x)@[k] + 4,
{
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            x@.len() == old(x)@.len(),
            forall |k:int| 0 <= k < i ==> #[trigger] x@[k] == old(x)@[k] + 4,
            forall |k:int| i <= k < x.len() ==> #[trigger] x@[k] == old(x)@[k],
    {
        /* code modified by LLM (iteration 1): fixed borrowing issue by reading value before setting */
        let val = x[i];
        x.set(i, val + 4);
        i += 1;
    }
}
}