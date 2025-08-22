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
            0 <= i <= x.len(),
            x@.len() == old(x)@.len(),
            forall |k:int| 0 <= k < i ==> #[trigger] x@[k] == old(x)@[k] + 4,
            forall |k:int| i <= k < x.len() ==> #[trigger] x@[k] == old(x)@[k],
            forall |k:int| 0 <= k < x.len() ==> old(x)@[k] <= 0x7FFF_FFFB,
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
        decreases x.len() - i
    {
        x[i] = x[i] + 4;
        i = i + 1;
    }
}
}