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
            0 <= i <= v.len(),
            exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1,
            /* code modified by LLM (iteration 1): added invariant to ensure odd element exists beyond current position */
            forall |j:int| 0 <= j < i ==> v[j] % 2 == 0
        /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
        decreases v.len() - i
    {
        if v[i] % 2 == 1 {
            return i;
        }
        i += 1;
    }
    /* code modified by LLM (iteration 1): replaced unreachable!() with assertion that leads to contradiction */
    assert(false);
    0
}
}