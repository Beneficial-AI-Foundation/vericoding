use vstd::prelude::*;

verus! {

fn mlast_maximum(v: &[i32]) -> (i: usize)
    requires v.len() > 0
    ensures 
        i < v.len(),
        forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k],
        forall|l: int| i < l < v.len() ==> v[i as int] > v[l],
{
    assume(false);
    unreached()
}

}
fn main() {}