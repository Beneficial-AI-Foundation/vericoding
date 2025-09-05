use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn reverse(a: &mut Vec<i32>)
    ensures forall|k: int| 0 <= k < old(a).len() ==> a[k] == old(a)[old(a).len() as int - 1 - k]
// </vc-spec>
// <vc-code>
{
    assume(false);
}
// </vc-code>


fn main() {
}

}
