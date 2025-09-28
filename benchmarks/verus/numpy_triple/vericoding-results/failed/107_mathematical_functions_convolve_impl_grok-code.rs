// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
 /* helper modified by LLM (iteration 5): no changes needed */ 
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
 /* code modified by LLM (iteration 5): fix overflows and invariant by using int for calculations and indexes */ 
{
    let a_seq = a@;
    let v_seq = v@;
    let len_: int = a_seq.len() + v_seq.len() - 1;
    let len = len_ as usize;
    let mut result = Vec::with_capacity(len);
    let mut k: int = 0;
    while k < len_
        invariant
            k <= len_,
            result.len() == k as usize,
            forall |j: int| 0 <= j < k ==> result@[j] == convolution_element_sum(a_seq, v_seq, j),
        decreases len_ - k
    {
        let mut sum: i32 = 0;
        let mut i: int = 0;
        while i < a_seq.len()
            invariant
                i <= a_seq.len(),
                sum == convolution_element_sum(a_seq.take(i), v_seq, k),
            decreases a_seq.len() - i
        {
            let idx_int = k - i;
            if idx_int >= 0 && idx_int < v_seq.len() {
                sum = sum + a[i as usize] * v[idx_int as usize];
            }
            i = i + 1;
        }
        result.push(sum);
        proof {
            assert(sum == convolution_element_sum(a_seq, v_seq, k));
        }
        k = k + 1;
    }
    result
}
// </vc-code>


}
fn main() {}