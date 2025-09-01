use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
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
    let mut result = Vec::new();
    let a_len = a.len();
    if a_len > 0 {
        result.push(a[0]);
    }
    let mut i = 1;
    while i < a_len
        invariant
            0 <= i <= a_len,
            result.len() == if i == 0 { 0 } else { i },
            forall |j: int, k: int| 0 <= j && j < k && k < result.len() ==> result[j] < result[k],
    {
        let last: i32 = *result.last().unwrap();
        let current: i32 = a[i];
        assert(last <= current);
        if current != last {
            assert(current != last);
            result.push(current);
            // After push, the new last is greater than previous last, maintaining strictness
        }
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}