// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma about convolution_element_sum for take(i+1) */
fn convolution_element_sum_take_succ(a: Seq<i32>, v: Seq<i32>, k: int, i: nat)
    requires
        i < a.len(),
    ensures
        convolution_element_sum(a.take(i + 1), v, k) == convolution_element_sum(a.take(i), v, k) + (if k >= i as int && k - i as int < v.len() as int { a[i as int] * v[k - i as int] } else { 0 }),
    decreases
        i
{
    proof {
        if i == 0 {
            // base case: take(1)
            assert(convolution_element_sum(a.take(1), v, k) == (if k >= 0 && k < v.len() as int { a[0] * v[k] } else { 0 }) + convolution_element_sum(a.take(0), v, k));
        } else {
            // unfold definition for a.take(i+1)
            assert(convolution_element_sum(a.take(i + 1), v, k) == (if k >= 0 && k < v.len() as int { (a.take(i + 1))[0] * v[k] } else { 0 }) + convolution_element_sum((a.take(i + 1)).skip(1), v, k));
            assert((a.take(i + 1))[0] == a[0]);
            assert((a.take(i + 1)).skip(1) == a.skip(1).take(i));
            // apply induction on the tail
            convolution_element_sum_take_succ(a.skip(1), v, k, i - 1);
            // relate indices: (a.skip(1))[i-1] == a[i]
            assert(a.skip(1)[(i - 1) as int] == a[i as int]);
            // conclude the desired equality
            assert(convolution_element_sum(a.take(i + 1), v, k) == convolution_element_sum(a.take(i), v, k) + (if k >= i as int && k - i as int < v.len() as int { a[i as int] * v[k - i as int] } else { 0 }));
        }
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
    /* code modified by LLM (iteration 5): implement convolution loops with invariants and lemma calls */
    let m = a.len();
    let n = v.len();
    let total = m + n - 1;
    let mut result: Vec<i32> = Vec::new();
    let mut k: nat = 0;
    while k < total
        invariant
            k <= total,
            result.len() == k,
            forall|t: int| 0 <= t && t < k as int ==> result[t as usize] == convolution_element_sum(a@, v@, t),
        decreases total - k
    {
        let mut sum: int = 0;
        let mut i: nat = 0;
        while i < m
            invariant
                i <= m,
                sum == convolution_element_sum((a@).take(i), v@, k as int),
            decreases m - i
        {
            if k as int >= i as int && k as int - i as int < n as int {
                let contrib: int = (a[i] as int) * (v[(k - i) as usize] as int);
                sum = sum + contrib;
                proof {
                    convolution_element_sum_take_succ(a@, v@, k as int, i);
                    assert(convolution_element_sum((a@).take(i + 1), v@, k as int) == convolution_element_sum((a@).take(i), v@, k as int) + (if k as int >= i as int && k as int - i as int < n as int { (a@)@[i as int] * v@[k as int - i as int] } else { 0 }));
                    assert(sum == convolution_element_sum((a@).take(i + 1), v@, k as int));
                }
            } else {
                proof {
                    convolution_element_sum_take_succ(a@, v@, k as int, i);
                    assert(sum == convolution_element_sum((a@).take(i + 1), v@, k as int));
                }
            }
            i = i + 1;
        }
        result.push(sum as i32);
        k = k + 1;
    }
    result
}
// </vc-code>


}
fn main() {}