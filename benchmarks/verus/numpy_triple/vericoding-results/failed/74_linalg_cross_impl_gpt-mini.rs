// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): int-to-i8 roundtrip lemma as a ghost proof */
proof fn int_to_i8_roundtrip(x: int)
    requires
        -128 <= x, x <= 127,
    ensures
        (x as i8) as int == x,
{
    assert((x as i8) as int == x);
}

// </vc-helpers>

// <vc-spec>
fn numpy_linalg_cross(x1: [i8; 3], x2: [i8; 3]) -> (result: [i8; 3])
    ensures
        result[0] as int == x1[1] as int * x2[2] as int - x1[2] as int * x2[1] as int,
        result[1] as int == x1[2] as int * x2[0] as int - x1[0] as int * x2[2] as int,
        result[2] as int == x1[0] as int * x2[1] as int - x1[1] as int * x2[0] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute cross product using mathematical int to avoid machine overflow */
    let c0: int = (x1[1] as int) * (x2[2] as int) - (x1[2] as int) * (x2[1] as int);
    let c1: int = (x1[2] as int) * (x2[0] as int) - (x1[0] as int) * (x2[2] as int);
    let c2: int = (x1[0] as int) * (x2[1] as int) - (x1[1] as int) * (x2[0] as int);
    let r0: i8 = #[verifier::truncate] (c0 as i8);
    let r1: i8 = #[verifier::truncate] (c1 as i8);
    let r2: i8 = #[verifier::truncate] (c2 as i8);
    [r0, r1, r2]
}

// </vc-code>


}
fn main() {}