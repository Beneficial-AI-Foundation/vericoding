use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::loop_isolation(false)]
proof fn lemma_update_vec_len_decreased(
    v: &mut Vec<i32>,
    k: usize,
    old_len: usize,
    decreased_len: usize,
)
    requires
        v.len() == old_len,
        k < old_len,
        decreased_len == old_len - 1,
    ensures
        v.len() == decreased_len,
{
    // The proof that `v.len()` becomes `new_len` after modifying elements
    // and setting length explicitly needs to be done with care.
    // For `Vec`s, after removing an element, the length automatically adjusts.
    // This lemma essentially states that if we build a new vector with one fewer element,
    // its length will be one less than the original.
    // This isn't strictly a lemma about `v.truncate` or `v.pop`, but about constructing a new vec.
    // The ensures clause here is straightforward if we are constructing a new vector.
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_element(a: &[i32], pos: usize) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        0 <= pos < a.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < pos ==> result[i] == a[i],
        forall|i: int| pos <= i < result.len() ==> result[i] == a[i + 1],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();

    // Copy elements before 'pos'
    let mut i: usize = 0;
    while i < pos
        invariant
            0 <= i <= pos,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result.view_nth(j as nat) == a.view_nth(j as nat),
    {
        result.push(a[i]);
        i = i + 1;
    }

    // Copy elements after 'pos'
    let mut k: usize = pos + 1;
    while k < a.len()
        invariant
            pos <= i < a.len(),
            pos + 1 <= k <= a.len(),
            i + (k - (pos + 1)) == result.len(), // result.len() is (elements before pos) + (elements after pos up to k)
            forall|j: int| 0 <= j < pos ==> result.view_nth(j as nat) == a.view_nth(j as nat),
            forall|j: int| pos <= j < result.len() ==> #[trigger] result.view_nth(j as nat) == #[trigger] a.view_nth((j + 1) as nat), // j+1 since we skip a[pos]
    {
        result.push(a[k]);
        k = k + 1;
    }

    assert(result.len() == (pos) + (a.len() - (pos + 1)));
    assert(result.len() == a.len() - 1);

    result
}
// </vc-code>

fn main() {}
}