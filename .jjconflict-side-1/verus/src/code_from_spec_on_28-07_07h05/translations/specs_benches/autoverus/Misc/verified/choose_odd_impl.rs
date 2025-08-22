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
        /* code modified by LLM (iteration 4): fixed invariant syntax by removing curly braces */
        invariant 
            0 <= i <= v.len(),
            exists |q:int| i <= q < v.len() && v[q] % 2 == 1
        /* code modified by LLM (iteration 4): added decreases clause to prove loop termination */
        decreases v.len() - i
    {
        if v[i] % 2 == 1 {
            return i;
        }
        i += 1;
    }
    /* code modified by LLM (iteration 4): replaced unreachable!() with return 0 and assertion that proves this case is impossible */
    assert(false);
    0
}
}