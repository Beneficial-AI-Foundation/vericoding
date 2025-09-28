// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): proof of division properties for triple using mathematical ints */
proof fn triple_correct(x: int, r: int)
    requires
        r == x * 3,
    ensures
        r / 3 == x,
        r / 3 * 3 == r
{
    // Use mathematical integer arithmetic in the proof to avoid executable overflow issues
    assert((x * 3) / 3 == x);
    assert(((x * 3) / 3) * 3 == x * 3);
}

// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute triple using int arithmetic and call proof helper */
    let result = (x as int * 3) as i32;
    proof {
        triple_correct(x as int, result as int);
    }
    result
}
// </vc-code>

}
fn main() {}