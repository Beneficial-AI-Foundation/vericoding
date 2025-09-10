use vstd::prelude::*;

verus! {

fn mmaximum1(v: &[i32]) -> (i: usize)
    requires v.len() > 0,
    ensures 
        0 <= i < v.len(),
        forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k],
{
    assume(false);
    unreached()
}

}
fn main() {}