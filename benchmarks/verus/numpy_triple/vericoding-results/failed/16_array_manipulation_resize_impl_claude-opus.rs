// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed indexing to use usize instead of int */
    let mut result: Vec<T> = Vec::new();
    if a.len() == 0 {
        return result;
    }
    let ghost orig_a = a@;
    let mut i: usize = 0;
    while i < new_size
        invariant
            i <= new_size,
            result.len() == i,
            a@ == orig_a,
            forall|j: int| 0 <= j < i ==> {
                if j < a.len() {
                    result[j] == a[j]
                } else {
                    result[j] == a[(j % a.len() as int) as int]
                }
            }
    {
        if i < a.len() {
            result.push(a[i]);
        } else {
            let idx = i % a.len();
            result.push(a[idx]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}