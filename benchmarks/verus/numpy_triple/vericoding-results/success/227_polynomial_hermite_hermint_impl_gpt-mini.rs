// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert u8 to nat for specs */
spec fn u8_to_nat(m: u8) -> nat { m as nat }
// </vc-helpers>

// <vc-spec>
fn hermint(c: Vec<f32>, m: u8, k: Vec<f32>, lbnd: f32, scl: f32) -> (result: Vec<f32>)
    requires 
        m > 0,
        k.len() == m as nat,
        c.len() > 0,
    ensures 
        result.len() == c.len() + m as nat,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): append m zeros to c with invariant tracking j and length */
    let mut result: Vec<f32> = c.clone();
    let mut j: u8 = 0;
    while j < m
        invariant
            result.len() == c.len() + u8_to_nat(j),
            j <= m,
        decreases
            u8_to_nat(m) - u8_to_nat(j)
    {
        result.push(0.0_f32);
        j = j + 1;
    }
    proof {
        assert(!(j < m));
        assert(j >= m);
        assert(j <= m);
        assert(j == m);
        assert(u8_to_nat(j) == u8_to_nat(m));
        assert(result.len() == c.len() + u8_to_nat(m));
    }
    result
}
// </vc-code>

}
fn main() {}