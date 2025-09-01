use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_copy(a: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut result: Vec<i32> = Vec::new();
    let old_a_len = a.len();

    let mut i: nat = 0;
    while (i as int) < (old_a_len as int)
        invariant
            0 <= i,
            i as int <= old_a_len as int,
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == a[j],
    {
        result.push(a[i]);
        i = i + 1;
    }

    assert(result.len() == old_a_len);
    assert(forall|k: int| 0 <= k && k < old_a_len ==> result[k] == a[k]);
    result
    // impl-end
}
// </vc-code>

fn main() {}
}