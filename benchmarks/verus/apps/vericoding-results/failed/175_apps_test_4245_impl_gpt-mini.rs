// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    a > 1 && b >= 0
}

spec fn sockets_after_strips(strips: int, a: int) -> int
    recommends a > 1 && strips >= 0
{
    1 + strips * (a - 1)
}

spec fn ceiling_division(x: int, y: int) -> int
    recommends y > 0
{
    if x % y == 0 {
        x / y
    } else if x >= 0 {
        x / y + 1
    } else {
        x / y
    }
}

spec fn min_strips_needed(a: int, b: int) -> int
    recommends valid_input(a, b)
{
    if b <= 1 {
        0
    } else {
        ceiling_division(b - 1, a - 1)
    }
}

spec fn correct_result(a: int, b: int, result: int) -> bool
    recommends valid_input(a, b)
{
    result >= 0 &&
    sockets_after_strips(result, a) >= b &&
    (result == 0 || sockets_after_strips(result - 1, a) < b)
}
// </vc-preamble>

// <vc-helpers>
fn lemma_sockets_incr(a: int, s: int)
    requires a > 1, s >= 0,
    ensures sockets_after_strips(s + 1, a) == sockets_after_strips(s, a) + (a - 1),
{
    proof {
        assert(sockets_after_strips(s + 1, a) == 1 + (s + 1) * (a - 1));
        assert(sockets_after_strips(s, a) == 1 + s * (a - 1));
        assert(1 + (s + 1) * (a - 1) == 1 + s * (a - 1) + (a - 1));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires valid_input(a as int, b as int)
    ensures correct_result(a as int, b as int, result as int)
// </vc-spec>
// <vc-code>
{
    let a_i = a as int;
    let b_i = b as int;

    if b_i <= 1 {
        result = 0;
        return result;
    }

    let mut strips: int = 0;
    while sockets_after_strips(strips, a_i) < b_i
        invariant
            strips >= 0,
            strips == 0 || sockets_after_strips(strips - 1, a_i) < b_i,
        decreases
            b_i - sockets_after_strips(strips, a_i)
    {
        let old = strips;
        strips = strips + 1;
        proof {
            assert(old >= 0);
            assert(sockets_after_strips(old, a_i) < b_i);
        }
    }

    proof {
        assert(strips >= 0);
        assert(sockets_after_strips(strips, a_i) >= b_i);
        if strips > 0 {
            assert(sockets_after_strips(strips - 1, a_i) < b_i);
        }
    }

    result = strips as i8;
    result
}
// </vc-code>


}

fn main() {}