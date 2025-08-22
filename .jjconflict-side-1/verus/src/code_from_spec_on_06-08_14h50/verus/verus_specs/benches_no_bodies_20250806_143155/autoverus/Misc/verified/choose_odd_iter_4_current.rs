use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)
    requires    
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1
    ensures
        odd_index < v.len(),
        v@[odd_index as int] % 2 == 1
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            exists |q:int| i <= q < v.len() && v[q] % 2 == 1
        /* code modified by LLM (iteration 2): added decreases clause for loop termination */
        decreases v.len() - i
    {
        if v[i] % 2 == 1 {
            return i;
        }
        i += 1;
    }
    /* code modified by LLM (iteration 2): replaced proof block with unreachable!() since the assertion approach may cause issues */
    unreachable!()
}
}