// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(k2: int, k3: int, k5: int, k6: int) -> bool {
    k2 >= 0 && k3 >= 0 && k5 >= 0 && k6 >= 0 &&
    k2 <= 5000000 && k3 <= 5000000 && k5 <= 5000000 && k6 <= 5000000
}

spec fn optimal_sum(k2: int, k3: int, k5: int, k6: int) -> int
    recommends valid_input(k2, k3, k5, k6)
{
    let count256 = if k2 <= k5 { if k2 <= k6 { k2 } else { k6 } } else { if k5 <= k6 { k5 } else { k6 } };
    let remaining_k2 = k2 - count256;
    let count32 = if k3 <= remaining_k2 { k3 } else { remaining_k2 };
    256 * count256 + 32 * count32
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide spec helpers for min2 and min3 */
spec fn min2(a: int, b: int) -> int { if a <= b { a } else { b } }
spec fn min3(a: int, b: int, c: int) -> int { min2(min2(a, b), c) }
// </vc-helpers>

// <vc-spec>
fn solve(k2: i8, k3: i8, k5: i8, k6: i8) -> (result: i8)
    requires 
        valid_input(k2 as int, k3 as int, k5 as int, k6 as int)
    ensures 
        result >= 0,
        result as int == optimal_sum(k2 as int, k3 as int, k5 as int, k6 as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute using machine integers and prove equality to spec using a proof block */
    let k2v: i64 = k2 as i64;
    let k3v: i64 = k3 as i64;
    let k5v: i64 = k5 as i64;
    let k6v: i64 = k6 as i64;

    let count256: i64 = if k2v <= k5v {
        if k2v <= k6v { k2v } else { k6v }
    } else {
        if k5v <= k6v { k5v } else { k6v }
    };
    let remaining_k2: i64 = k2v - count256;
    let count32: i64 = if k3v <= remaining_k2 { k3v } else { remaining_k2 };
    let sum: i64 = 256 * count256 + 32 * count32;
    let result: i8 = sum as i8;

    proof {
        let k2i: int = k2 as int;
        let k3i: int = k3 as int;
        let k5i: int = k5 as int;
        let k6i: int = k6 as int;
        assert(sum as int == optimal_sum(k2i, k3i, k5i, k6i));
    }

    result
}
// </vc-code>


}

fn main() {}