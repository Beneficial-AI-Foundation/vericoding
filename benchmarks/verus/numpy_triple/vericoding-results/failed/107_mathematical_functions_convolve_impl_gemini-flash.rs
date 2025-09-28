// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No change. */

// </vc-helpers>

// <vc-spec>
spec fn convolution_element_sum(a: Seq<i32>, v: Seq<i32>, k: int) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        let i = 0;
        let contribution = if k >= i && k - i < v.len() {
            a[i] * v[k - i]
        } else {
            0
        };
        contribution + convolution_element_sum(a.skip(1), v, k)
    }
}

fn numpy_convolve(a: Vec<i32>, v: Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0 && v.len() > 0,
    ensures 
        result.len() == a.len() + v.len() - 1,
        forall|k: int| 0 <= k < result.len() ==> result[k] == convolution_element_sum(a@, v@, k),
        result[0] == a[0] * v[0],
        result[result.len() - 1] == a[a.len() - 1] * v[v.len() - 1],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Resolved `nat` and `int` type mismatch by casting `v.len()` to `usize` before comparing with `(k_idx - i_idx)`. Also, made `k_idx` and `i_idx` `usize` type for direct use with `len()` and indexing. */
{
    let len_a = a.len();
    let len_v = v.len();
    let len_res = len_a + len_v - 1;
    let mut result: Vec<i32> = Vec::new();
    result.reserve(len_res);

    let mut k_idx: usize = 0;
    while k_idx < len_res
        invariant
            k_idx <= len_res,
            result.len() == k_idx,
            result.capacity() >= len_res,
            forall|j: int| 0 <= j < k_idx as int ==> result@[j] == convolution_element_sum(a@, v@, j),
    {
        let mut current_sum: i32 = 0;
        let mut i_idx: usize = 0;
        while i_idx < len_a
            invariant
                k_idx < len_res,
                i_idx <= len_a,
                current_sum as int == convolution_element_sum(a@.subsequence(0, i_idx as int), v@, k_idx as int),
        {
            let val_k_minus_i = k_idx.checked_sub(i_idx);
            if let Some(mut val) = val_k_minus_i {
                if val < len_v {
                    current_sum = current_sum + a.get(i_idx).unwrap() * v.get(val).unwrap();
                }
            }
            i_idx = i_idx + 1;
        }

        result.push(current_sum);
        k_idx = k_idx + 1;
    }

    result
}
// </vc-code>


}
fn main() {}