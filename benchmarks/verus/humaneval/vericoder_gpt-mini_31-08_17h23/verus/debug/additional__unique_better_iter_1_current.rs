use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique_better(a: &[i32]) -> (result: Vec<i32>)
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
    let n: usize = a.len();
    if n == 0 {
        return vec![];
    }
    let mut result: Vec<i32> = Vec::new();
    result.push(a[0]);
    let mut i: usize = 1;
    while i < n
        invariant
            i <= n,
            1 <= result.len(),
            result.len() <= i,
            forall |p: usize, q: usize|
                #![trigger result[p], result[q]]
                p < q && q < result.len() ==> result[p] < result[q],
    {
        let prev_len = result.len();
        let last = result[prev_len - 1];
        let cur = a[i];
        if cur > last {
            result.push(cur);
            proof {
                // After push, result.len() == prev_len + 1
                assert(result.len() == prev_len + 1);
                // Show strictness still holds:
                // For any p < q < result.len(), either q < prev_len (old indices) and
                // the property follows from the invariant, or q == prev_len (new last)
                // and then for p == prev_len-1 we have last < cur, and for p < prev_len-1
                // we have result[p] < last < cur by invariant + cur > last.
                //
                // We prove the universal property by cases on q.
                assert(forall |p: usize, q: usize|
                    #![trigger result[p], result[q]]
                    p < q && q < result.len() ==>
                        result[p] < result[q]
                );
                // The verifier can discharge the above from the previous invariant,
                // the fact cur > last, and basic transitivity of <.
            }
        }
        i = i + 1;
        // Ensure the loop invariant relation result.len() <= i holds at the top of next iteration
        assert(result.len() <= i);
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}