// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    a > 0 && b > 0
}

spec fn count_squares(a: int, b: int) -> int
    recommends a >= 0 && b >= 0
    decreases a + b when a > 0 && b > 0
{
    if a == 0 || b == 0 {
        0
    } else if a > b {
        if b == 0 { 0 } else {
            a / b + count_squares(a % b, b)
        }
    } else if b > a {
        if a == 0 { 0 } else {
            b / a + count_squares(a, b % a)
        }
    } else {
        1
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove count_squares <= a + b */
proof fn count_squares_le_sum(a: int, b: int)
    requires a >= 0, b >= 0,
    ensures count_squares(a, b) <= a + b,
{
    if a == 0 || b == 0 {
        // count_squares returns 0, trivially <= a + b
    } else if a > b {
        count_squares_le_sum(a % b, b);
        proof {
            let c = count_squares(a, b);
            assert(c == a / b + count_squares(a % b, b));
            assert(count_squares(a % b, b) <= (a % b) + b);
            assert(a / b + (a % b) <= a);
            assert(c <= a + b);
        }
    } else if b > a {
        count_squares_le_sum(a, b % a);
        proof {
            let c = count_squares(a, b);
            assert(c == b / a + count_squares(a, b % a));
            assert(count_squares(a, b % a) <= a + (b % a));
            assert(b / a + (b % a) <= b);
            assert(c <= a + b);
        }
    } else {
        // a == b, count_squares(a,a) == 1 <= a + a
    }
}

/* helper modified by LLM (iteration 5): prove count_squares is non-negative */
proof fn count_squares_nonneg(a: int, b: int)
    requires a >= 0, b >= 0,
    ensures count_squares(a, b) >= 0,
{
    if a == 0 || b == 0 {
        // returns 0
    } else if a > b {
        count_squares_nonneg(a % b, b);
    } else if b > a {
        count_squares_nonneg(a, b % a);
    } else {
        // a == b, returns 1 >= 0
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires valid_input(a as int, b as int)
    ensures 
        result >= 0,
        a == b ==> result == 1,
        a > b ==> result >= 1,
        result as int == count_squares(a as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): recursive Euclidean decomposition matching spec */
    if a == b {
        1
    } else if a > b {
        let q: i8 = a / b;
        let r: i8 = a % b;
        if r == 0 {
            proof {
                // a = q*b, so count_squares(a,b) = a / b = q
                assert((q as int) == (a as int) / (b as int));
                assert(count_squares(a as int, b as int) == (a as int) / (b as int));
                assert((q as int) == count_squares(a as int, b as int));
            }
            q
        } else {
            proof {
                // r = a % b and r > 0, so recursive call preconditions hold
                assert(r as int > 0);
                assert((b as int) > 0);
            }
            let sub: i8 = solve(r, b);
            let res: i8 = q + sub;
            proof {
                // by induction sub as int == count_squares(r,b)
                assert((sub as int) == count_squares(r as int, b as int));
                assert((q as int) == (a as int) / (b as int));
                assert((a as int) / (b as int) + count_squares(r as int, b as int) == count_squares(a as int, b as int));
                assert((res as int) == count_squares(a as int, b as int));
            }
            res
        }
    } else {
        // b > a
        let q: i8 = b / a;
        let r: i8 = b % a;
        if r == 0 {
            proof {
                assert((q as int) == (b as int) / (a as int));
                assert(count_squares(a as int, b as int) == (b as int) / (a as int));
                assert((q as int) == count_squares(a as int, b as int));
            }
            q
        } else {
            proof {
                assert(r as int > 0);
                assert((a as int) > 0);
            }
            let sub: i8 = solve(a, r);
            let res: i8 = q + sub;
            proof {
                assert((sub as int) == count_squares(a as int, r as int));
                assert((q as int) == (b as int) / (a as int));
                assert((b as int) / (a as int) + count_squares(a as int, r as int) == count_squares(a as int, b as int));
                assert((res as int) == count_squares(a as int, b as int));
            }
            res
        }
    }
}

// </vc-code>


}

fn main() {}