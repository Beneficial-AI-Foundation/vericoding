// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn rotate_right(l: &Vec<i32>, n: usize) -> (result: Vec<i32>)
    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> {
            let len = l.len() as int;
            let rotated_index = ((i - n as int + len) % len) as int;
            #[trigger] result[i] == l[rotated_index]
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type errors in the loop invariant by removing 'as usize' cast, ensuring integer comparison. */
{
    let l_len = l.len();
    if l_len == 0 {
        return Vec::new();
    }

    let n_wrapped = n % l_len;
    let mut result_vec: Vec<i32> = Vec::new();
    result_vec.reserve(l_len);

    let mut i = 0;
    while i < l_len
        invariant
            0 <= i <= l_len,
            result_vec.len() == i,
            forall |j: int| 0 <= j < i ==> {
                let len = l_len as int;
                let rotated_index = (j - n_wrapped as int + len) % len;
                #[trigger] result_vec[j] == l[rotated_index]
            }
        decreases l_len - i
    {
        // Calculate the original index. (i - n_wrapped + l_len) ensures positive result for modulo.
        let original_index = (i + (l_len - n_wrapped)) % l_len;
        result_vec.push(l[original_index]);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}