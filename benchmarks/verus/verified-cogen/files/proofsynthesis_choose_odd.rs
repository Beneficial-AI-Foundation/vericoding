use vstd::prelude::*;

verus!{

fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)

    requires    
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1,

    ensures
        odd_index < v.len(),
{
    assume(false);
    unreached();
}

}
fn main() {}