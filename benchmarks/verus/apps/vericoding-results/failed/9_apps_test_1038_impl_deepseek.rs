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
/* helper modified by LLM (iteration 5): Fixed type conversion issues and added executable helper functions */
fn highest_power_of_two_executable(n: i32) -> i32 {
    if n <= 0 {
        return 0;
    }
    let mut power: i32 = 1;
    while power * 2 <= n {
        power *= 2;
    }
    power
}

fn count_set_bits_executable(a: i32, b: i32, bit: i32) -> i32 {
    if bit <= 0 {
        return 0;
    }
    let full_cycles: i32 = (b - a + 1) / (2 * bit);
    let remainder: i32 = (b - a + 1) % (2 * bit);
    let ones_in_full_cycle: i32 = full_cycles * bit;
    let ones_in_remainder: i32 = if remainder > bit { remainder - bit } else { 0 };
    ones_in_full_cycle + ones_in_remainder
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
{
    /* code modified by LLM (iteration 5): Fixed type conversion issues by using executable helpers */
    if a == b {
        return a;
    }
    
    let max_power_val: i32 = highest_power_of_two_executable(b);
    let mut result: i32 = 0;
    
    let mut i = max_power_val;
    while i > 0
        invariant
            result >= 0,
            i >= 0
    {
        let count: i32 = count_set_bits_executable(a, b, i);
        if count % 2 == 1 {
            result |= i;
        }
        i /= 2;
    }
    
    result
}
// </vc-code>

}

fn main() {}