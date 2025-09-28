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
/* helper modified by LLM (iteration 4): implement using mathematical formula for XOR range */
fn compute_xor_range(a: u32, b: u32) -> (result: u32)
    requires
        a <= b
    ensures
        result as int == xor_range(a as int, b as int)
{
    if a == b {
        a
    } else {
        let xor_a_minus_1 = if a == 0 { 0 } else { xor_0_to_n(a - 1) };
        let xor_b = xor_0_to_n(b);
        xor_a_minus_1 ^ xor_b
    }
}

/* helper modified by LLM (iteration 5): implement xor_0_to_n recursively to match spec definition */
fn xor_0_to_n(n: u32) -> (result: u32)
    ensures result as int == xor_range(0, n as int)
    decreases n
{
    if n == 0 {
        0
    } else {
        let prev = xor_0_to_n(n - 1);
        prev ^ n
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
/* code modified by LLM (iteration 5): use recursive helper functions */
{
    let a_u = a as u32;
    let b_u = b as u32;
    let result = compute_xor_range(a_u, b_u);
    result as i32
}
// </vc-code>

}

fn main() {}