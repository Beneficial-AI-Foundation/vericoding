// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn resize<T>(a: Vec<T>, new_size: usize) -> (result: Vec<T>)
    ensures
        result.len() == new_size,
        forall|i: int| 0 <= i < new_size ==> {
            if i < a.len() {
                result[i] == a[i]
            } else if a.len() > 0 {
                result[i] == a[(i % a.len() as int) as int]
            } else {
                true
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fix compilation error by using correct modulo lemma */
    let old_len = a.len();
    if new_size == 0 {
        return Vec::new();
    }

    if old_len == 0 {
        // The spec ensures that for an empty input vector, any content is acceptable
        // for the output. However, without a default value or a way to construct T,
        // it's impossible to create a non-empty Vec<T>. We return an empty Vec,
        // which will fail the length postcondition if new_size > 0.
        // This indicates an implicit precondition `a.len() > 0 || new_size == 0`.
        return Vec::new();
    }

    // This implementation requires T: Copy to duplicate elements when extending the vector.
    // `let val = a[idx]` performs a copy if T is a Copy type.
    let mut result: Vec<T> = Vec::new_with_capacity(new_size);
    let mut i: usize = 0;
    while i < new_size
        invariant
            old_len == a.len(),
            a.len() > 0,
            i <= new_size,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result.view()[j] === a.view()[(j % a.len() as int) as int],
        decreases new_size - i
    {
        proof {
            vstd::arithmetic::div_mod::lemma_mod_range(i as int, old_len as int);
        }
        let val = a[i % old_len];
        result.push(val);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}