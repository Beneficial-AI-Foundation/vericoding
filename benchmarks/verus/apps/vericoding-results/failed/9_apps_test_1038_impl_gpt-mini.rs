// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_input(a: int, b: int) -> bool {
        0 <= a <= b
    }
    
    spec fn xor_int(x: int, y: int) -> int
        decreases x + y
    {
        if x >= 0 && y >= 0 {
            if x == 0 && y == 0 { 0 }
            else if x == 0 { y }
            else if y == 0 { x }
            else {
                let bit_x = x % 2;
                let bit_y = y % 2;
                let xor_bit: int = if bit_x != bit_y { 1 } else { 0 };
                xor_bit + 2 * xor_int(x / 2, y / 2)
            }
        } else {
            0
        }
    }
    
    spec fn xor_range(a: int, b: int) -> int
        decreases b - a
    {
        if 0 <= a <= b {
            if a == b { a }
            else { xor_int(a, xor_range(a + 1, b)) }
        } else {
            0
        }
    }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relates i32 xor to spec xor_int */
proof fn xor_corresponds_i32(x: i32, y: i32)
    requires
        x >= 0,
        y >= 0,
    ensures
        (x ^ y) as int == xor_int(x as int, y as int),
    decreases
        x as int + y as int,
{
    if x == 0 {
        assert (0 ^ y == y);
        assert (xor_int(0 as int, y as int) == y as int);
        assert ((0 ^ y) as int == xor_int(0 as int, y as int));
    } else if y == 0 {
        assert (x ^ 0 == x);
        assert (xor_int(x as int, 0 as int) == x as int);
        assert ((x ^ 0) as int == xor_int(x as int, 0 as int));
    } else {
        let bx: i32 = x % 2;
        let by: i32 = y % 2;
        let xr: i32 = x / 2;
        let yr: i32 = y / 2;
        xor_corresponds_i32(xr, yr);
        let xor_bit: i32 = if bx != by { 1 } else { 0 };
        assert (((xr ^ yr) as int) == xor_int(xr as int, yr as int));
        assert ((x ^ y) as int == xor_bit as int + 2 * ((xr ^ yr) as int));
        assert (xor_int(x as int, y as int) == xor_bit as int + 2 * xor_int(xr as int, yr as int));
        assert ((x ^ y) as int == xor_int(x as int, y as int));
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i32, b: i32) -> (result: i32)
    requires 
        a >= 0,
        b >= 0,
        a <= b
    ensures 
        result >= 0,
        result as int == xor_range(a as int, b as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): iterate from b down to a accumulating xor */
{
    let mut j: i32 = b;
    let mut acc: i32 = 0;

    while j >= a
        invariant
            a >= 0,
            b >= 0,
            a <= b,
            j >= a - 1,
            j <= b,
            acc as int == xor_range((j + 1) as int, b as int),
        decreases
            j - a + 1
    {
        let old_acc: i32 = acc;
        acc = j ^ old_acc;

        proof {
            xor_corresponds_i32(j, old_acc);
            assert (old_acc as int == xor_range((j + 1) as int, b as int));
            assert ((j ^ old_acc) as int == xor_int(j as int, old_acc as int));
            assert (xor_int(j as int, old_acc as int) == xor_range(j as int, b as int));
            assert (acc as int == xor_range(j as int, b as int));
        }

        j -= 1;
    }

    proof {
        assert (acc as int == xor_range(a as int, b as int));
        assert (xor_range(a as int, b as int) >= 0);
        assert (acc as int >= 0);
        assert (acc >= 0);
    }

    acc
}

// </vc-code>

}

fn main() {}