use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
#[cfg(test)]
pub fn array_to_vec<T: Copy>(a: &[T]) -> Vec<T> {
    a.to_vec()
}
// </vc-helpers>

// <vc-spec>
fn reverse(a: &[i32]) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let old_a = a.to_vec(); // Capture `a` as a Vec for use in post-conditions and invariants
    let a_len = a.len();

    // If a is empty, result should be empty.
    // The loop handles this correctly, but explicitly asserting is good for clarity.
    if a_len == 0 {
        return result;
    }

    // Initialize result with a_len elements (e.g., zeros)
    // This part is crucial for the post-condition `result.len() == a.len()`
    // and for indexing `result` later.
    // Verus requires `Vec::new()` and then `push` or `insert`
    // or direct initialization if capacity is known.
    // For simplicity, we can push elements during the loop.

    // Loop from the end of `a` to the beginning
    let mut i: usize = a_len; // Change type to usize
    while i > 0
        invariant
            0 <= i && i <= a_len, // No need for casting
            result.len() == a_len - i,
            forall|j: int| 0 <= j && j < result.len() ==>
                #[trigger] result[j] == old_a[a_len - 1 - j],
    {
        i = i - 1;
        result.push(old_a[i]); // No need for casting
    }

    result
}
// </vc-code>

fn main() {}
}