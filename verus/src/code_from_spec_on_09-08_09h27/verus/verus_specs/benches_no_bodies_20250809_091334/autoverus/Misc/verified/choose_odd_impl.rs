// The function is supposed to find an index of an odd number in the vector. The precondition guarantees that such an odd number exists, but the loop invariant needs to be strengthened to ensure that if we haven't returned yet, there's still an odd number in the remaining portion of the vector.

use vstd::prelude::*;
fn main() {}

verus!{
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)
    requires    
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1
    ensures
        odd_index < v.len(),
        v[odd_index as int] % 2 == 1
{
    let mut i: usize = 0;
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while i < v.len()
        invariant
            i <= v.len(),
            exists |q:int| i <= q < v.len() && v[q] % 2 == 1
        decreases v.len() - i
    {
        if v[i] % 2 == 1 {
            return i;
        }
        i += 1;
    }
    /* code modified by LLM (iteration 1): replaced unreachable code with proof block showing contradiction */
    proof {
        assert(i == v.len());
        assert(exists |q:int| i <= q < v.len() && v[q] % 2 == 1);
        assert(false);
    }
    0
}
}