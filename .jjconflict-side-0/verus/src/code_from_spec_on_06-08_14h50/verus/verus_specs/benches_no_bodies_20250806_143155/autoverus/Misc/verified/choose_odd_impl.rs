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
        decreases v.len() - i
    {
        if v[i] % 2 == 1 {
            return i;
        }
        i += 1;
    }
    /* code modified by LLM (iteration 3): replaced unreachable!() with proof block showing contradiction */
    proof {
        assert(i == v.len());
        assert(exists |q:int| i <= q < v.len() && v[q] % 2 == 1);
        assert(forall |q:int| i <= q < v.len() ==> false);
        assert(false);
    }
    0 // This line is unreachable but needed for compilation
}
}