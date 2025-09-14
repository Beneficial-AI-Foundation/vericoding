// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)

    requires 
        old(y).len() == 0,

    ensures 
        forall |k:int| 0 <= k < y.len() ==> y[k] % 3 == 0 && x@.contains(y@[k]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added a decreases clause to the while loop to prove termination */
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            forall|k: int| 0 <= k < y.len() ==> y@[k] % 3 == 0 && x@.contains(y@[k]),
        decreases x.len() - i
    {
        let item = x[i];
        if item % 3 == 0 {
            y.push(item);
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}