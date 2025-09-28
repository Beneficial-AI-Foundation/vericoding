// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= b
}

spec fn gcd_of_range(a: int, b: int) -> int
    recommends valid_input(a, b)
{
    if a == b { a } else { 1 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple properties of gcd_of_range */
proof fn gcd_of_range_props(a: int, b: int)
    requires
        valid_input(a, b),
    ensures
        a == b ==> gcd_of_range(a, b) == a,
        a < b ==> gcd_of_range(a, b) == 1,
{
    if a == b {
        assert(gcd_of_range(a, b) == a);
    } else {
        assert(gcd_of_range(a, b) == 1);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int)
    ensures 
        result as int == gcd_of_range(a as int, b as int),
        a == b ==> result as int == a as int,
        a < b ==> result as int == 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute result by cases and return it */
    if a == b {
        let result: i8 = a;
        proof {
            gcd_of_range_props(a as int, b as int);
            assert(gcd_of_range(a as int, b as int) == a as int);
        }
        result
    } else {
        let result: i8 = 1_i8;
        proof {
            gcd_of_range_props(a as int, b as int);
            assert(gcd_of_range(a as int, b as int) == 1);
        }
        result
    }
}

// </vc-code>


}

fn main() {}