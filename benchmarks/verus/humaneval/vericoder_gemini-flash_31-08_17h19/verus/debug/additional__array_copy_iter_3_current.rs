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

    let mut i: usize = 0; // Change to usize for loop counter
    while i < old_a_len
        invariant
            0 <= i,
            i <= old_a_len,
            result.len() == i,
            forall|j: int| 0 <= j && (j as usize) < i ==> result[j as usize] == a[j as usize],
    {
        result.push(a[i]);
        i = i + 1;
    }

    assert(result.len() == old_a_len);
    assert(forall|k: int| 0 <= k && (k as usize) < old_a_len ==> result[k as usize] == a[k as usize]);
    result
    // impl-end
}
// </vc-code>

fn main() {}
}