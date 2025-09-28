// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 0 && k >= 0 && k + 1 > 0
}

spec fn valid_output(result: Seq<int>, n: int, k: int) -> bool {
    result.len() == 3 &&
    result[0] >= 0 && result[1] >= 0 && result[2] >= 0 &&
    result[1] == result[0] * k &&
    result[0] + result[1] <= n / 2 &&
    result[2] == n - result[0] - result[1]
}

spec fn optimal_diplomas(n: int, k: int) -> int
    recommends valid_input(n, k)
{
    (n / 2) / (k + 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: Vec<i8>)
    requires valid_input(n as int, k as int)
    ensures 
        valid_output(result@.map(|i, x| x as int), n as int, k as int) &&
        result@[0] as int == optimal_diplomas(n as int, k as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): replaced ghost function call with non-ghost arithmetic computation */
{
    let n_val = n as i16;
    let k_val = k as i16;

    // Bounds from precondition and i8 range
    assert(n_val >= 0 && n_val <= 127);
    assert(k_val >= 0 && k_val <= 127);

    // Compute a = (n/2) / (k+1) using integer arithmetic
    let a = (n_val / 2) / (k_val + 1);
    assert(a >= 0 && a <= 63);   // because (n/2) <= 63, and k+1>=1, so a<=63

    let b = a * k_val;
    // We know that a*(k_val+1) <= n_val/2 (by the definition of integer division, because a = floor((n_val/2)/(k_val+1)) so a*(k_val+1) <= n_val/2)
    // So a+b = a*(k_val+1) <= n_val/2 <= 63
    assert(a * (k_val+1) <= n_val/2);
    assert(a + b <= n_val/2);
    assert(n_val/2 <= 63);   // because n_val<=127 -> n_val/2 <= 63

    let c = n_val - a - b;
    assert(c >= 0);

    // Now, we know a in [0,63], b in [0,63] (because a+b<=63), and c in [0,127] (because n_val<=127 and a+b<=63 -> c>=127-63=64? Actually, n_val can be as low as 0, but then a=0, b=0, c=0. So c is nonnegative and at most 127).

    let a_i8 = a as i8;
    let b_i8 = b as i8;
    let c_i8 = c as i8;

    vec![a_i8, b_i8, c_i8]
}
// </vc-code>


}

fn main() {}