use vstd::prelude::*;
fn main() {}

verus!{

pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
requires 
    old(y).len() == 0,
ensures 
    forall |k:int| 0 <= k < y.len() ==> y[k] % 3 == 0 && x@.contains(y@[k]),
{
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            forall |k:int| 0 <= k < y.len() ==> y[k] % 3 == 0 && x@.contains(y@[k]),
        /* code modified by LLM (iteration 1): added decreases clause to fix compilation error */
        decreases x.len() - i
    {
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
        i += 1;
    }
}

}