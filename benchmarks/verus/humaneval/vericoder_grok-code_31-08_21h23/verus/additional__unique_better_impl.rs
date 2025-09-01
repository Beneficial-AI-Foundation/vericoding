use vstd::prelude::*;

verus! {

// <vc-helpers>

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
            forall |j: int, k: int| #![trigger (result@)[j], (result@)[k]]
                0 <= j && j < k && k < result.len() ==> (result@)[j] < (result@)[k],
        decreases (a_len as int - (i as int))
    {
        let last_index_exec = result.len() - 1;
        let last: i32 = result[last_index_exec];
        let current: i32 = a[i];
        if current != last {
            let old_len = result.len();
            result.push(current);
            proof {
                let last_index = (old_len - 1) as int;
                let new_last = (result@)[last_index];
                let new_index = (old_len) as int;
                let pushed = (result@)[new_index];
                assert(pushed == a[i]);
                assert(new_last == (result@)[last_index]);
                assert(new_last < pushed);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}