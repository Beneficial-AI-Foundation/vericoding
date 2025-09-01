use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut res: Vec<i32> = Vec::new();
    let mut idxs: Vec<nat> = Vec::new();
    let mut i: nat = 0;
    while i < a.len()
        invariant i <= a.len();
        invariant idxs.len() == res.len();
        invariant forall |p: int| 0 <= p && p < res.len() ==>
            0 <= idxs[p] && idxs[p] < i && res[p] == a[idxs[p]];
        invariant forall |p: int, q: int| 0 <= p && p < q && q < res.len() ==>
            idxs[p] < idxs[q];
        invariant forall |p: int, q: int| 0 <= p && p < q && q < res.len() ==>
            res[p] < res[q];
        decreases a.len() - i;
    {
        let ai: i32 = a[i];
        if idxs.len() == 0 {
            // empty result: just push
            res.push(ai);
            idxs.push(i);
        } else {
            let last_pos: nat = idxs[idxs.len() - 1];
            let last_val: i32 = res[res.len() - 1];
            if last_val != ai {
                // prove last_val < ai using monotonicity of a and mapping invariant
                proof {
                    // last_pos < i by invariant mapping
                    assert(last_pos < i);
                    // i < a.len() holds by loop guard
                    assert(i < a.len());
                    // by precondition (monotonicity) a[last_pos] <= a[i]
                    assert(a[last_pos] <= a[i]);
                    // last_val == a[last_pos] by mapping invariant
                    assert(last_val == a[last_pos]);
                    // last_val != a[i] by branch condition
                    assert(last_val != a[i]);
                    // combine to get last_val < a[i]
                    assert(last_val < a[i]);
                }
                // push new unique value and its index
                res.push(ai);
                idxs.push(i);
            }
        }
        i = i + 1;
    }
    res
    // impl-end
}
// </vc-code>

fn main() {}
}