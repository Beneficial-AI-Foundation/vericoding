// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, b: int) -> bool {
    n > 0 && a > 0 && b > 0
}

spec fn valid_output(result: Seq<int>, n: int, a: int, b: int) -> bool {
    result.len() == 3 &&
    result[0] >= 6 * n &&
    result[1] > 0 && result[2] > 0 &&
    result[0] == result[1] * result[2] &&
    ((result[1] >= a && result[2] >= b) || (result[1] >= b && result[2] >= a))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): total ceil_div for positive integers */
spec fn ceil_div(x: int, y: int) -> int {
    if y <= 0 {
        0
    } else if x <= 0 {
        0
    } else {
        (x + y - 1) / y
    }
}

/* helper modified by LLM (iteration 4): integer max */
spec fn imax(x: int, y: int) -> int {
    if x >= y { x } else { y }
}

/* helper modified by LLM (iteration 4): integer min */
spec fn imin(x: int, y: int) -> int {
    if x <= y { x } else { y }
}

/* helper modified by LLM (iteration 4): lemma about positive i8 bounds */
proof fn lemma_i8_pos_range(x: i8)
    requires
        x as int > 0,
    ensures
        1 <= x as int,
        x as int <= 127,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8) -> (result: Vec<i8>)
    requires valid_input(n as int, a as int, b as int)
    ensures valid_output(result@.map(|i, x| x as int), n as int, a as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): avoid overflow via explicit bounds and i32 arithmetic with assertions */
    let mut v: Vec<i8> = Vec::new();

    let big: i8 = if a >= b { a } else { b };
    let small: i8 = if a >= b { b } else { a };

    let ni: i16 = n as i16;
    let big16: i16 = big as i16;
    let small16: i16 = small as i16;

    proof {
        // Input ranges from i8
        assert((n as int) >= 1 && (n as int) <= 127);
        assert((a as int) >= 1 && (a as int) <= 127);
        assert((b as int) >= 1 && (b as int) <= 127);
        assert((big as int) >= 1 && (big as int) <= 127);
        assert((small as int) >= 1 && (small as int) <= 127);
    }

    // Compute 6*n safely in i32
    let ni32: i32 = n as i32;
    proof {
        // For i32 multiplication by 6 to be safe, |ni32| <= i32::MAX / 6 holds trivially since |ni32| <= 127
        assert(-357913941 <= ni32 && ni32 <= 357913941);
    }
    let need32: i32 = 6 * ni32;

    // Safe bounds for i32 multiplication big16 * small16
    proof {
        assert(-46340 <= big16 as i32 && big16 as i32 <= 46340);
        assert(-46340 <= small16 as i32 && small16 as i32 <= 46340);
    }
    let base_prod32: i32 = (big16 as i32) * (small16 as i32);

    let mut t32: i32 = 0;
    if base_prod32 < need32 {
        // Bound the intermediate arithmetic to avoid overflow
        proof {
            // need32 in [6, 762]
            assert(6 <= need32 && need32 <= 762);
            // base_prod32 in [1, 16129]
            assert(1 <= base_prod32 && base_prod32 <= 16129);
            // big16 in [1, 127]
            assert(1 <= big16 && big16 <= 127);
            // Therefore the numerator is within i32 range comfortably
            // Lower bound: 6 - 16129 + 1 - 1 = -16123
            // Upper bound: 762 - 1 + 127 - 1 = 887
        }
        let numerator: i32 = need32 - base_prod32 + (big16 as i32) - 1;
        let denom: i32 = if big16 as i32 > 0 { big16 as i32 } else { 1 };
        let q: i32 = numerator / denom;
        t32 = if q < 0 { 0 } else { q };
    }

    let f1_32: i32 = big16 as i32;
    let f2_32: i32 = (small16 as i32) + t32;

    // y is within i8 range already
    let y: i8 = if f1_32 > 127 { 127 } else { if f1_32 < -128 { -128 } else { f1_32 as i8 } };
    // z may exceed i8; clamp to remain within range
    let z: i8 = if f2_32 > 127 { 127 } else { if f2_32 < -128 { -128 } else { f2_32 as i8 } };

    // Compute product safely in i32
    proof {
        assert(-46340 <= y as i32 && y as i32 <= 46340);
        assert(-46340 <= z as i32 && z as i32 <= 46340);
    }
    let prod32: i32 = (y as i32) * (z as i32);
    let x: i8 = if prod32 > 127 { 127 } else { if prod32 < -128 { -128 } else { prod32 as i8 } };

    v.push(x);
    v.push(y);
    v.push(z);
    v
}
// </vc-code>


}

fn main() {}