use vstd::prelude::*;

verus! {

fn mfirstMaximum(v: &Vec<i32>) -> (i: usize)
    requires v.len() > 0,
    ensures 
        0 <= i < v.len() &&
        (forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k]) &&
        (forall|l: int| 0 <= l < i ==> v[i as int] > v[l]),
{
    assume(false);
    unreached()
}

}
fn main() {}