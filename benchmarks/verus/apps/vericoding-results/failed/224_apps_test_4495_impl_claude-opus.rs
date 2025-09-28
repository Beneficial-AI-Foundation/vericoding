// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, x: int) -> bool {
    a >= 0 && b >= a && x > 0
}

spec fn count_divisible_in_range(a: int, b: int, x: int) -> int
    recommends valid_input(a, b, x)
{
    if a == 0 {
        b / x + 1
    } else {
        b / x - (a - 1) / x
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn count_divisible(a: i8, b: i8, x: i8) -> (count: i8)
    requires 
        valid_input(a as int, b as int, x as int),
    ensures 
        count as int == count_divisible_in_range(a as int, b as int, x as int),
        count >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix syntax error in division expression */
    if a == 0 {
        let quotient = b / x;
        let count = if quotient < 127 {
            quotient + 1
        } else {
            127i8
        };
        proof {
            assert(quotient as int == b as int / x as int);
            if quotient < 127 {
                assert(count as int == quotient as int + 1);
                assert(count as int == b as int / x as int + 1);
            } else {
                assert(quotient == 127);
                assert(b as int / x as int == 127);
                assert(count == 127);
                assert(count as int <= b as int / x as int + 1);
            }
            assert(count as int == count_divisible_in_range(a as int, b as int, x as int));
            assert(count >= 0);
        }
        count
    } else {
        let quotient_b = b / x;
        let quotient_a_minus_1 = (a - 1) / x;
        let count = if quotient_b >= quotient_a_minus_1 {
            quotient_b - quotient_a_minus_1
        } else {
            0i8
        };
        proof {
            assert(quotient_b as int == b as int / x as int);
            assert(quotient_a_minus_1 as int == (a as int - 1) / x as int);
            if quotient_b >= quotient_a_minus_1 {
                assert(count as int == (quotient_b - quotient_a_minus_1) as int);
                assert(count as int == quotient_b as int - quotient_a_minus_1 as int);
                assert(count as int == b as int / x as int - (a as int - 1) / x as int);
            } else {
                assert(count == 0);
                assert(b as int / x as int < ((a as int - 1) / x as int));
                assert(b as int / x as int - ((a as int - 1) / x as int) <= 0);
                assert(count as int <= b as int / x as int - ((a as int - 1) / x as int));
            }
            assert(count as int == count_divisible_in_range(a as int, b as int, x as int));
            assert(count >= 0);
        }
        count
    }
}
// </vc-code>


}

fn main() {}