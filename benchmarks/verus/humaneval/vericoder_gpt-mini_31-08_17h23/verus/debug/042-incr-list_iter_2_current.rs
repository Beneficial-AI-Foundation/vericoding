use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this verification.
// </vc-helpers>

// <vc-spec>
fn incr_list(l: Vec<i32>) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int| 0 <= i < l.len() ==> l[i] + 1 <= i32::MAX,
    // pre-conditions-end

    // post-conditions-start
    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> #[trigger] result[i] == l[i] + 1,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut res: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < l.len() {
        invariant 0 <= i;
        invariant i <= l.len();
        invariant res.len() == i;
        invariant forall|k: int| 0 <= k < i ==> #[trigger] res[k] == l[k] + 1;
        let v = l[i] + 1;
        res.push(v);
        i += 1;
    }
    res
    // impl-end
}
// </vc-code>

fn main() {}
}