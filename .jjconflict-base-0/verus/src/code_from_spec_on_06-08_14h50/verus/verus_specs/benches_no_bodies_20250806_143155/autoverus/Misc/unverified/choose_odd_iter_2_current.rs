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
            exists |q:int| i <= q < v.len() && v[q] % 2 == 1
    {
        if v[i] % 2 == 1 {
            return i;
        }
        i += 1;
    }
    /* code modified by LLM (iteration 1): replaced unreachable!() with return 0 and added proof that this case is impossible */
    proof {
        assert(i == v.len());
        assert(exists |q:int| i <= q < v.len() && v[q] % 2 == 1);
        assert(false);
    }
    0
}
}