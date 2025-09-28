// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added invariant and verification improvements */
proof fn convolution_element_sum_equivalent(a: Seq<i32>, v: Seq<i32>, k: int)
    ensures convolution_element_sum(a, v, k) == convolution_element_sum_helper(a, v, k, 0, a.len() as int)
    decreases a.len()
{
    if a.len() > 0 {
        convolution_element_sum_equivalent(a.skip(1), v, k);
    }
}

spec fn convolution_element_sum_helper(a: Seq<i32>, v: Seq<i32>, k: int, idx: int, len: int) -> int
    decreases len - idx
{
    if idx >= len {
        0
    } else {
        let contribution = if k >= idx && k - idx < v.len() {
            a[idx] * v[k - idx]
        } else {
            0
        };
        contribution + convolution_element_sum_helper(a, v, k, idx + 1, len)
    }
}
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
{
    /* code modified by LLM (iteration 5): Added decreases clause to outer while loop */
    let a_len = a.len();
    let v_len = v.len();
    let mut result = Vec::new();
    let result_len = a_len + v_len - 1;
    result.resize(result_len, 0);
    
    let ghost old_result = result@;
    
    let mut k: usize = 0;
    while k < result_len
        invariant
            k <= result_len,
            result.len() == result_len,
            forall|i: int| 0 <= i < k ==> result[i] == convolution_element_sum(a@, v@, i),
            forall|i: int| 0 <= i < result_len ==> result@[i] == old_result[i],
            result[0] == a[0] * v[0],
            result[result_len - 1] == a[a_len - 1] * v[v_len - 1],
        decreases result_len - k
    {
        let mut sum = 0;
        let mut i: usize = 0;
        while i < a_len
            invariant
                i <= a_len,
                sum == convolution_element_sum_helper(a@, v@, k as int, 0, i as int),
            decreases a_len - i
        {
            if k >= i && k - i < v_len {
                sum = sum + a[i] * v[k - i];
            }
            i = i + 1;
        }
        proof {
            convolution_element_sum_equivalent(a@, v@, k as int);
        }
        result[k] = sum;
        k = k + 1;
    }
    result
}
// </vc-code>


}
fn main() {}