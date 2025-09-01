use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
fn max_element(a: &Vec<i32>) -> (max: i32)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut i: usize = 1;
    let mut cur: i32 = a[0];

    while i < a.len() {
        invariant i >= 1usize;
        invariant i <= a.len();
        invariant forall |k: int| 0 <= k && k < i as int ==> a@[k] <= cur;
        invariant exists |j: int| 0 <= j && j < i as int && a@[j] == cur;
        decreases a.len() - i;

        let ai: i32 = a[i];
        if ai > cur {
            cur = ai;
        }

        i += 1;
    }

    // From the invariants and loop exit, we have i == a.len(),
    // so the invariants give the required postconditions.
    assert(forall |k: int| 0 <= k && k < a.len() as int ==> a@[k] <= cur);
    assert(exists |j: int| 0 <= j && j < a.len() as int && a@[j] == cur);

    cur
    // impl-end
}
// </vc-code>

fn main() {}
}