// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove i8 range bounds */
fn i8_bounds(x: i8)
    ensures
        -128 <= x as int,
        x as int <= 127,
{
    assert(-128 <= x as int);
    assert(x as int <= 127);
}

// </vc-helpers>

// <vc-spec>
fn lagroots(c: Vec<i8>) -> (roots: Vec<i8>)
    requires
        c.len() >= 2,
        c@[c.len() - 1 as int] != 0,
    ensures
        c.len() == 2 ==> roots.len() == 1,
        c.len() == 2 ==> roots@[0] as int == 1 + c@[0] as int / c@[1] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute single root for degree-1 polynomial using integer arithmetic with truncate */
    let mut roots: Vec<i8> = Vec::new();
    if c.len() == 2 {
        let a: i8 = c[0];
        let b: i8 = c[1];
        let r_int: int = 1 + (a as int) / (b as int);
        let r_i8: i8 = #[verifier::truncate] r_int as i8;
        roots.push(r_i8);
        proof {
            assert(c.len() == 2);
            assert(roots.len() == 1);
            assert(roots@[0] as int == r_int);
        }
    }
    roots
}

// </vc-code>

}
fn main() {}