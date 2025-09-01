use vstd::prelude::*;

verus! {

// <vc-helpers>
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
    let a_len = a.len();

    // If a is empty, result should be empty.
    // The loop handles this correctly, but explicitly asserting is good for clarity.
    if a_len == 0 {
        return result;
    }

    // Loop from the end of `a` to the beginning
    let mut i: usize = a_len;
    while i > 0
        invariant
            0 <= i && i <= a_len,
            result.len() == a_len - i,
            forall|j: int| 0 <= j && j < result.len() ==>
                #[trigger] result[j] == a[a_len - 1 - j],
    {
        i = i - 1;
        result.push(a[i]);
    }

    result
}
// </vc-code>

fn main() {}
}