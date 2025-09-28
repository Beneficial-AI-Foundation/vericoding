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
/* helper modified by LLM (iteration 5): The helper function `xor_formula` has been modified to handle `int` inputs. The mod operations are now `int` operations. The `nat` return type has been changed to `int` to align with the change and avoid warnings from Verus. */
spec fn xor_formula(x: int) -> int {
    if x < 0 { 0 }
    else if x % 4 == 0 { x }
    else if x % 4 == 1 { 1 }
    else if x % 4 == 2 { x + 1 }
    else { 0 }
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
/* code modified by LLM (iteration 5): This iteration is a retry of the 'XOR of numbers in a range' problem. The current implementation directly computes the XOR sum using the `xor_formula` helper and integer XOR. The primary change in this iteration is to fix the compilation errors by ensuring that `xor_formula` can be called without casting `i32` values to `int` inside the `xor_formula` calls. Instead, the `i32` values are converted to `int` variables, and then these `int` variables are passed to `xor_formula`. The result of the `xor_formula` calls are then XORed together and cast back to `i32`.*/
{
    let a_val: int = a as int;
    let b_val: int = b as int;

    let result = (xor_formula(b_val) ^ xor_formula(a_val - 1)) as i32;
    result
}
// </vc-code>

}

fn main() {}