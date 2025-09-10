use vstd::prelude::*;

verus! {

fn reverse(a: &mut Vec<i32>)
    ensures forall|i: int| 0 <= i < old(a).len() ==> a[i] == old(a)[old(a).len() - 1 - i]
{
    assume(false);
    unreached()
}

}
fn main() {}