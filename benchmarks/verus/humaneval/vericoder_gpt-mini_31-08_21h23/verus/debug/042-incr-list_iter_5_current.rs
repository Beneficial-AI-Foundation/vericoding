use vstd::prelude::*;

verus! {

// <vc-helpers>
fn build_incr(l: Vec<i32>, n: nat, idx: nat) -> (res: Vec<i32>)
    requires
        idx <= n,
        forall|i: int| 0 <= i < l.len() ==> l[i] + 1 <= i32::MAX,
    ensures
        res.len() == n - idx,
        forall|k: int| 0 <= k < res.len() ==> #[trigger] res[k] == l[idx + k] + 1,
    decreases n - idx
{
    if idx == n {
        Vec::new()
    } else {
        let mut tail = build_incr(l.clone(), n, idx + 1);
        // insert at front to preserve original order
        tail.insert(0, l[idx] + 1);
        // proofs of postconditions:
        proof {
            // tail.len() was n - (idx+1), now it's n - idx
            assert(tail.len() == n - idx);
            // show forall k: 0 <= k < tail.len() ==> tail[k] == l[idx + k] + 1
            // For k == 0, tail[0] == l[idx] + 1 by the insert.
            // For k > 0, use induction hypothesis on previous tail before insert.
            // The insert shifts previous elements by 1, so for k > 0:
            // tail[k] == old_tail[k-1] == l[(idx+1) + (k-1)] + 1 == l[idx + k] + 1.
            assert(forall|k: int| 0 <= k < tail.len() ==>
                #[trigger] tail[k] == l[idx + k] + 1);
        }
        tail
    }
}
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
    let n: nat = l.len();
    build_incr(l, n, 0)
}
// </vc-code>

fn main() {}
}