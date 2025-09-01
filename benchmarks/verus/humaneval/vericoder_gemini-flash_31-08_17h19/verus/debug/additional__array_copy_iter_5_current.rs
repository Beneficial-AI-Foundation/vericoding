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
    let mut result: Vec<i32> = Vec::new();
    let old_a_len = a.len();

    let mut i: usize = 0;
    while i < old_a_len
        invariant
            0 <= i as int,
            i as int <= old_a_len as int,
            result.len() == i,
            forall|j: int| 0 <= j && (j as usize) < i ==> result.spec_index(j) == a.spec_index(j),
    {
        result.push(a.index(i));
        i = i + 1;
    }

    assert(result.len() == old_a_len);
    assert(forall|k: int| 0 <= k && (k as usize) < old_a_len ==> result.spec_index(k) == a.spec_index(k));
    result
}
// </vc-code>

fn main() {}
}