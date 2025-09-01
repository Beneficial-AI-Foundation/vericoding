use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
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
    let mut result: Vec<i32> = Vec::new();
    if a.len() == 0 {
        return result;
    }
    result.push(a[0]);
    let mut i: usize = 1;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() >= 1,
            forall|k: int| #[trigger result[k], result[k+1]] 0 <= k && k < result.len() - 1 ==> result[k] < result[k + 1],
    {
        if a[i] != result[result.len() - 1] {
            proof {
                assert(a[i] != result[result.len() - 1]);
                assert(forall|p: int, q: int| #[trigger a[p], a[q]] p < q && 0 <= p <= i ==> a[p] <= a[q] == result[result.len()-1] <= a[i]);
                assert(a[i] > result[result.len() - 1]);
            }
            result.push(a[i]);
            proof {
                assert(result[result.len() - 2] < result[result.len() - 1]);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}