use vstd::prelude::*;

verus!{
fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
    // pre-conditions-start
    requires 
        old(y).len() == 0,
    // pre-conditions-end
    // post-conditions-start
    ensures 
        forall |k:int| 0 <= k < y.len() ==> y[k] % 3 == 0 && x@.contains(y@[k]),
    // post-conditions-end
{
    for i in 0..x.len()
        invariant
            forall |k:int| 0 <= k < y.len() ==> y[k] % 3 == 0 && x@.contains(y@[k]),
    {
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
    }
}
}

fn main() {}