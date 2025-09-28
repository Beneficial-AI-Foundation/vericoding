// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mid(p: int, q: int) -> (m: int)

    requires 
        p <= q,
    ensures 
        p <= m <= q,
        m - p <= q - m,
        0 <= (q - m) - (m - p) <= 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatches by casting integer literals to `int` and changed ghost variables to exec. */
    let d = q - p;
    let mut d_div_2: int = 0;
    let mut temp: int = 0;
    while temp + (2 as int) <= d
        invariant
            d == q - p,
            d >= 0,
            d_div_2 >= 0,
            temp == d_div_2 * 2,
            temp <= d,
        decreases d - temp
    {
        d_div_2 = d_div_2 + (1 as int);
        temp = temp + (2 as int);
    }
    p + d_div_2
}
// </vc-code>

}
fn main() {}