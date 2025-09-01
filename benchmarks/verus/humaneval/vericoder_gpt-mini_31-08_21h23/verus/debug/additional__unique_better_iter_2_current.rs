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
    let mut last_idx: Option<nat> = Option::None;

    while k < n
        invariant { k <= n }
        invariant {
            forall |i: int, j: int|
                #![trigger result[i], result[j]]
                0 <= i && i < j && j < (result.len() as int) ==> result@[i] < result@[j]
        }
        invariant {
            match last_idx {
                None => result.len() == 0,
                Some(li) => {
                    li < k && result@[((result.len() as int) - 1)] == a@[(li as int)]
                }
            }
        }
    {
        match last_idx {
            None => {
                // no element taken yet; always take the first encountered
                result.push(a[k]);
                last_idx = Some(k);
            }
            Some(li) => {
                // li < k holds by invariant
                if a[k] > a[li] {
                    // strictly greater than last taken -> push
                    result.push(a[k]);
                    last_idx = Some(k);
                }
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