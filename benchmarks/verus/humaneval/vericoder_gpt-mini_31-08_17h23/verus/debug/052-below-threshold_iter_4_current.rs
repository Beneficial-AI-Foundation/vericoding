use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
fn below_threshold(l: &[i32], t: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int| 0 <= i < l.len() ==> l[i] < t,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut i: int = 0;
    let n: int = l.len() as int;
    let mut res: bool = true;
    while i < n
        invariant 0 <= i && i <= n;
        invariant res == (forall|j: int| 0 <= j && j < i ==> l[j as usize] < t);
    {
        let cur: i32 = l[i as usize];
        res = res && (cur < t);
        i += 1;
    }
    proof {
        assert(res == (forall|j: int| 0 <= j && j < n ==> l[j as usize] < t));
    }
    res
    // impl-end
}
// </vc-code>

fn main() {}
}