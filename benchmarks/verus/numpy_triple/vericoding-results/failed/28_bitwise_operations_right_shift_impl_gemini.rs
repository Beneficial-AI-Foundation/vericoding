// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Corrected the invalid lemma name. */
fn shift_right_impl(a: i32, b: i32) -> (r: i32)
    requires b >= 0
    ensures r == a >> b
{
    if b < 32 {
        let r = a >> b;
        proof {
            if a >= 0 {
                vstd::bitvector::lemma_shr_is_div_pow2(a as u32, b as u32);
            }
        }
        r
    } else if a >= 0 {
        0
    } else {
        -1
    }
}
// </vc-helpers>

// <vc-spec>
fn right_shift(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            &&& (x1[i] >= 0 ==> result[i] == x1[i] / (1i32 << x2[i]))
            &&& (x1[i] < 0 ==> result[i] == x1[i] >> x2[i])
            &&& (x2[i] == 0 ==> result[i] == x1[i])
            &&& (x1[i] > 0 ==> result[i] >= 0)
            &&& (x1[i] < 0 ==> result[i] <= 0)
            &&& (x1[i] == 0 ==> result[i] == 0)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Added a proof block to establish the loop invariant. */
{
    let mut result = Vec::with_capacity(x1.len() as usize);
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            forall|k: int| 0 <= k < x2.len() ==> x2[k] >= 0,
            0 <= i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> {
                let v1 = x1[j];
                let v2 = x2[j];
                let r = result[j];
                &&& (v1 >= 0 ==> r == v1 / (1i32 << v2))
                &&& (v1 < 0 ==> r == v1 >> v2)
                &&& (v2 == 0 ==> r == v1)
                &&& (v1 > 0 ==> r >= 0)
                &&& (v1 < 0 ==> r <= 0)
                &&& (v1 == 0 ==> r == 0)
            }
    {
        let v1 = x1[i];
        let v2 = x2[i];
        let r = v1 >> v2;

        proof {
            if v1 >= 0 && v2 < 32 {
                vstd::bitvector::lemma_shr_is_div_pow2(v1 as u32, v2 as u32);
            }
        }

        result.push(r);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}