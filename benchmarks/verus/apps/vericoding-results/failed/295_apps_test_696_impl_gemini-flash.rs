// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(p: int) -> bool {
    2 <= p < 2000
}

spec fn count_primitive_roots(p: int) -> int
    recommends valid_input(p)
{
    if p == 2 { 
        1 
    } else { 
        /* Count of integers i where 1 <= i < p-1 and 
           for all j where 2 <= j <= i, not ((p-1) % j == 0 && i % j == 0) */
        Set::new(|i: int| 1 <= i < p-1 && (forall|j: int| 2 <= j <= i ==> !((p-1) % j == 0 && #[trigger] (i % j) == 0))).len() as int
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed `ghost` keyword from `a` and `b` parameters in `gcd` to fix compilation error. */
spec fn gcd(a: int, b: int) -> int
    decreases a, b
{
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(p: i8) -> (result: i8)
    requires valid_input(p as int)
    ensures 
        result >= 0 &&
        result as int == count_primitive_roots(p as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes to the code body; the previous fix was for a compilation error in a helper function. */
{
    let ghost p_int = p as int;
    if p_int == 2 {
        return 1;
    }

    let mut count: i8 = 0;
    let ghost p_minus_1 = (p_int - 1);

    let mut i: i8 = 1;
    while (i as int) <= p_minus_1
        invariant
            1 <= (i as int),
            (i as int) <= p_minus_1,
            count as int == Set::new(|k: int| 1 <= k && k < i as int && gcd(k, p_int - 1) == 1).len() as int,
            valid_input(p_int),
        decreases (p_minus_1 - (i as int))
    {
        if gcd(i as int, p_minus_1) == 1 {
            count = count + 1;
        }
        i = i + 1;
    }

    count
}
// </vc-code>


}

fn main() {}