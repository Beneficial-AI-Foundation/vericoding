// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100 && 1 <= d <= 100
}

spec fn can_communicate(a: int, b: int, c: int, d: int) -> bool {
    (if a - c >= 0 { a - c } else { c - a }) <= d || 
    (((if a - b >= 0 { a - b } else { b - a }) <= d) && 
     ((if b - c >= 0 { b - c } else { c - b }) <= d))
}
// </vc-preamble>

// <vc-helpers>
spec fn abs_diff(x: int, y: int) -> int { if x - y >= 0 { x - y } else { y - x } }

/* helper modified by LLM (iteration 5): relate i8 abs diff to spec abs_diff */
fn abs_diff_i8(a: i8, b: i8)
    requires
        1 <= a as int <= 100, 1 <= b as int <= 100,
    ensures
        (if a >= b { a - b } else { b - a }) as int == abs_diff(a as int, b as int),
{
    if a >= b {
        proof {
            assert((a as int) >= (b as int));
            assert((a as int) - (b as int) >= 0);
            assert(abs_diff(a as int, b as int) == (a as int) - (b as int));
        }
    } else {
        proof {
            assert((b as int) > (a as int));
            assert((b as int) - (a as int) >= 0);
            assert(abs_diff(a as int, b as int) == (b as int) - (a as int));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: String)
    requires 
        valid_input(a as int, b as int, c as int, d as int),
    ensures 
        result@ == seq!['Y', 'e', 's'] <==> can_communicate(a as int, b as int, c as int, d as int),
        result@ == seq!['Y', 'e', 's'] || result@ == seq!['N', 'o'],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute communication and return "Yes"/"No" using vstd::string::string_from_str */
    let diff_ac: i8 = if a >= c { a - c } else { c - a };
    let diff_ab: i8 = if a >= b { a - b } else { b - a };
    let diff_bc: i8 = if b >= c { b - c } else { c - b };

    let comm: bool = diff_ac <= d || (diff_ab <= d && diff_bc <= d);

    proof {
        abs_diff_i8(a, c);
        abs_diff_i8(a, b);
        abs_diff_i8(b, c);
        let ai: int = a as int;
        let bi: int = b as int;
        let ci: int = c as int;
        let di: int = d as int;
        assert((if a >= c { a - c } else { c - a }) as int == abs_diff(ai, ci));
        assert((if a >= b { a - b } else { b - a }) as int == abs_diff(ai, bi));
        assert((if b >= c { b - c } else { c - b }) as int == abs_diff(bi, ci));
        assert((d as int) == di);
        assert(comm == can_communicate(ai, bi, ci, di));
    }

    if comm {
        vstd::string::string_from_str("Yes")
    } else {
        vstd::string::string_from_str("No")
    }
}

// </vc-code>


}

fn main() {}