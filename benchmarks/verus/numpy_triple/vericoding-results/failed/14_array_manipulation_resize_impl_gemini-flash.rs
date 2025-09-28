// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed an incorrect type `Vector` and fixed syntax by removing `pub proof` which is not allowed. */
fn contains_value_at_index<T>(v: &Vec<T>, i: int, val: T)
    requires
        0 <= i,
        i < v.len(),
    ensures
        v[i] == val,
{}
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
/* code modified by LLM (iteration 5): Fixed type mismatch issues by using `result_vec.push(*a.get(i as usize).unwrap());` and `result_vec.push(*a.get((i as int % a_len as int) as usize).unwrap());` to unwrap the Option<&T> returned by `a.get()` and then dereference. Also, fixed the invariant `forall` clause by correctly casting `a_len` to `int` before the modulo operation, as it is used within an `int` context. */
{
    let mut result_vec: Vec<T> = Vec::new();
    let a_len = a.len();

    if new_size == 0 {
        return result_vec;
    }

    // Copy existing elements up to new_size or a_len
    let mut i = 0;
    while i < a_len && i < new_size
        invariant 
            0 <= i,
            a_len == a.len(),
            new_size == new_size,
            result_vec.len() == i,
            forall|j: int| 0 <= j && j < i ==> 
                a.len() > j ==> result_vec[j as usize] == a[j as usize]
    {
        result_vec.push(*a.get(i as usize).unwrap());
        i += 1;
    }

    // Fill remaining elements based on a.len()
    if a_len > 0 {
        while i < new_size
            invariant
                i <= new_size,
                result_vec.len() == i,
                a_len == a.len(),
                forall|k: int| 0 <= k && k < i ==> {
                    if k < a_len {
                        result_vec[k as usize] == a[k as usize]
                    } else {
                        result_vec[k as usize] == a[(k as int % a_len as int) as usize]
                    }
                }
        {
            result_vec.push(*a.get((i as int % a_len as int) as usize).unwrap());
            i += 1;
        }
    }

    result_vec
}
// </vc-code>

}
fn main() {}