// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn source_index(a_len: usize, i: usize) -> Option<usize> { if a_len == 0 { None } else { Some(i % a_len) } }
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
    let mut result: Vec<T> = Vec::new();
    let alen = a.len();
    while result.len() < new_size
        invariant result.len() <= new_size,
        invariant forall|j: int| 0 <= j < result.len() as int ==> {
            if (j as usize) < alen {
                result[j as usize] == a[j as usize]
            } else if alen > 0 {
                result[j as usize] == a[(j as usize % alen) as usize]
            } else {
                true
            }
        },
        decreases new_size - result.len()
    {
        if alen == 0 {
            // When the input vector is empty, we can only construct an empty result.
            // The specification allows arbitrary contents in this case, but we cannot
            // fabricate values of type T. Enforce new_size == 0 so we return an empty vec.
            assert(new_size == 0);
        } else {
            let idx: usize = result.len() % alen;
            result.push(a[idx].clone());
        }
    }
    result
}
// </vc-code>

}
fn main() {}