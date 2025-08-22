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
            exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1
    {
        if v[i] % 2 == 1 {
            return i;
        }
        i += 1;
    }
    unreachable!()
}
}