use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
    let mut result: Vec<i32> = Vec::new();
    let mut k: nat = 0;
    let n: nat = a.len();
    let mut last_idx: nat = 0;
    let mut taken: bool = false;

    while k < n
        invariant { k <= n }
        invariant {
            forall |i: int, j: int|
                #![trigger result[i], result[j]]
                0 <= i && i < j && j < (result.len() as int) ==> result@[i] < result@[j]
        }
        invariant { !taken ==> result.len() == 0 }
        invariant { taken ==> last_idx < k }
        invariant { taken ==> result@[((result.len() as int) - 1)] == a@[(last_idx as int)] }
    {
        if !taken {
            // no element taken yet; always take the first encountered
            result.push(a[k]);
            last_idx = k;
            taken = true;
        } else {
            // taken implies last_idx < k by invariant
            if a[k] > a[last_idx] {
                // strictly greater than last taken -> push
                result.push(a[k]);
                last_idx = k;
            }
        }
        k = k + 1;
    }

    proof {
        // At loop exit k == n and invariant gives the desired strictness property.
        assert(forall |i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < (result.len() as int) ==> result@[i] < result@[j]
        );
    }

    result
    // impl-end
}
// </vc-code>

fn main() {}
}