use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn swap_first_and_last(a: &mut Vec<i32>)
    requires 
        old(a).len() > 0,
    ensures
        a.len() == old(a).len(),
        a[0] == old(a)[old(a).len() - 1],
        a[a.len() - 1] == old(a)[0],
        forall|k: int| 1 <= k < old(a).len() - 1 ==> a[k] == old(a)[k],
// </vc-spec>
// <vc-code>
{
    let old_a = a.clone();
    let n: usize = old_a.len();

    if n > 1 {
        let tmp = a[n - 1];
        a[n - 1] = a[0];
        a[0] = tmp;
    }

    proof {
        assert(a.len() == old_a.len());

        if n == 1 {
            assert(a[0] == old_a[0]);
            assert(a[n - 1] == old_a[0]);
        } else {
            assert(a[0] == old_a[n - 1]);
            assert(a[n - 1] == old_a[0]);
        }

        assert(forall|k: int| 1 <= k && k < (n as int) - 1 ==>
            (a@)[k] == (old_a@)[k]);
    }
}
// </vc-code>

fn main() {
}

}