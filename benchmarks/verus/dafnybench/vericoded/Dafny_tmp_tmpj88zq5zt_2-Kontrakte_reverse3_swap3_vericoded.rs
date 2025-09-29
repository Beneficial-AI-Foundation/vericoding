use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn swap3(a: &mut Vec<i32>, h: usize, i: usize, j: usize)
    requires 
        h < old(a).len(),
        i < old(a).len(),
        j < old(a).len(),
        i != j && j != h && h != i,
    ensures
        a[h as int] == old(a)[i as int],
        a[j as int] == old(a)[h as int],
        a[i as int] == old(a)[j as int],
        forall|k: int| 0 <= k < old(a).len() && k != h as int && k != i as int && k != j as int ==> a[k] == old(a)[k],
        a.len() == old(a).len(),
// </vc-spec>
// <vc-code>
{
    let old_seq = a.clone();
    // perform 3-cycle: h <- i, i <- j, j <- h using a temporary
    let tmp: i32 = a[h];
    a[h] = a[i];
    a[i] = a[j];
    a[j] = tmp;

    proof {
        // length preserved by element assignments
        assert(a.len() == old_seq.len());

        // the three specified positions are updated to the correct old values
        assert(a@[h as int] == old_seq@[i as int]);
        assert(a@[j as int] == old_seq@[h as int]);
        assert(a@[i as int] == old_seq@[j as int]);

        // all other positions are unchanged
        assert(forall|k: int| 0 <= k && k < (old_seq.len() as int) && k != h as int && k != i as int && k != j as int ==>
            a@[k] == old_seq@[k]);
    }
}
// </vc-code>

fn main() {}

}