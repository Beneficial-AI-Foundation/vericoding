// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec alias for 2^e avoiding executable overflow */
spec fn pow2(e: nat) -> int { pow(2, e) }
// </vc-helpers>

// <vc-spec>
fn left_shift(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == x1[i] * pow(2, x2[i] as nat),
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == 0,
        forall|i: int| 0 <= i < result.len() && x1[i] > 0 && x2[i] > 0 ==> result[i] > x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] < 0 && x2[i] > 0 ==> result[i] < x1[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement using left-shift and relate to pow via specification */
    let n = x1.len();
    let mut result: Vec<i32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            x1.len() == n,
            x2.len() == n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == x1[j] * pow(2, x2[j] as nat),
        decreases n - i
    {
        let i_int: int = i as int;
        assert(0 <= i_int && i_int < x2.len() as int);
        assert(x2[i_int] >= 0);
        let e_usize: usize = x2[i_int] as usize;
        let v_i: i32 = x1[i_int] << e_usize;
        proof {
            assert((x1[i_int] << e_usize) as int == (x1[i_int] as int) * pow(2, (x2[i_int] as nat)));
        }
        result.push(v_i);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}