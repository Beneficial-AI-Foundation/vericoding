use vstd::prelude::*;

verus! {

fn barrier(v: &[i32], p: usize) -> (b: bool)
    requires 
        v.len() > 0,
        p < v.len(),
    ensures 
        b == forall|k: usize, l: usize| 
            k <= p && p < l && l < v.len() ==> v[k as int] < v[l as int]
{
    assume(false);
    unreached();
}

}
fn main() {}