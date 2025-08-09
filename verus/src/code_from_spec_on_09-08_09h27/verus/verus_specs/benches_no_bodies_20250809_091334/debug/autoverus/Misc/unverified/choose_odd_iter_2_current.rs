use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)
    requires    
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1
    ensures
        odd_index < v.len()
{
    let mut i = 0;
    while i < v.len()
        invariant 
            i <= v.len(),
            exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1,
            /* code modified by LLM (iteration 1): added invariant to ensure odd number exists in remaining range */
            exists |q:int| i <= q < v.len() && v[q] % 2 == 1
    {
        if v[i] % 2 == 1 {
            return i;
        }
        i += 1;
    }
    /* code modified by LLM (iteration 1): replaced unreachable!() with assert false proof since loop invariant guarantees we find odd number */
    proof {
        assert(false);
    }
    0
}
}