use vstd::prelude::*;
fn main() {}
verus!{
//IMPL myfun2
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
            /* code modified by LLM (iteration 1): added invariant to preserve precondition for overflow safety */
            forall |k:int| i <= k < x.len() ==> x@[k] <= 0x7FFF_FFFB,
        /* code modified by LLM (iteration 1): added decreases clause for termination */
        decreases x.len() - i
    {
        /* code modified by LLM (iteration 1): read value before mutable borrow and add overflow check */
        let old_val = x[i];
        assert(old_val <= 0x7FFF_FFFB); // From invariant
        assert(old_val + 4 <= 0x7FFF_FFFF); // Overflow safety
        x.set(i, old_val + 4);
        /* code modified by LLM (iteration 1): added assertion to help prove invariant maintenance */
        assert(forall |k:int| 0 <= k < i + 1 ==> #[trigger] x@[k] == old(x)@[k] + 4);
        i += 1;
    }
}
}