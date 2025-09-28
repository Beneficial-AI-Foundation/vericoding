// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(h: int, a: int) -> bool {
    h >= 1 && a >= 1
}

spec fn is_minimum_attacks(attacks: int, h: int, a: int) -> bool {
    attacks >= 1 &&
    attacks * a >= h &&
    (attacks - 1) * a < h
}

spec fn ceil_div(h: int, a: int) -> int
    recommends a > 0
{
    (h + a - 1) / a
}
// </vc-preamble>

// <vc-helpers>

proof fn ceil_div_is_minimum_attacks(h: int, a: int)
    requires
        h >= 1,
        a >= 1
    ensures
        is_minimum_attacks(ceil_div(h, a), h, a)
{
    let d = ceil_div(h, a);
    assert(d * a >= h) by {
        assert(a > 0);
        assert((h + a - 1) / a * a >= h);
        assert({ let r = (h - 1) % a + 1; d * a == h + a - r });
    }
    assert((d - 1) * a < h) by {
        let d1 = d - 1;
        assert(d >= 1) by {
            assert(h <= d * a);
            assert(h >= 1);
        }
        assert(d1 * a == (h + a - 1) / a * a - a);
        assert(d1 * a < h);
    }
}

fn to_i8_checked(n: int) -> (res: i8)
    requires
        n >= i8::MIN as int,
        n <= i8::MAX as int
    ensures
        res as int == n
{
    let res: i8 = n as i8;
    proof { assert(res@ == n); }
    res
}

// </vc-helpers>

// <vc-spec>
fn solve(h: i8, a: i8) -> (attacks: i8)
    requires 
        valid_input(h as int, a as int)
    ensures 
        is_minimum_attacks(attacks as int, h as int, a as int),
        attacks as int == ceil_div(h as int, a as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix compilation by moving ghost code to proper proof block */
    let result: i8;
    proof {
        let h_int: int = h as int;
        let a_int: int = a as int;
        ceil_div_is_minimum_attacks(h_int, a_int);
        let div = ceil_div(h_int, a_int);
        assert(div >= 1) by {
            assert(h_int >= 1 && a_int >= 1);
            assert(div * a_int >= h_int);
        };
        assert(div <= i8::MAX as int) by {
            assert(h_int <= i8::MAX as int && a_int >= 1);
        };
        result = to_i8_checked(div);
    }
    result
}
// </vc-code>


}

fn main() {}