// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `gcd` and `lcm_recursive` to operate on `int` inputs and return `int` results, aligned with the `spec` functions and `i32` use in `lcm` vector. */
fn gcd(a: int, b: int) -> (result: int)
    requires a >= 0,
             b >= 0
{
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else if a == b {
        a
    } else if a > b {
        gcd(a - b, b)
    } else {
        gcd(a, b - a)
    }
}

fn lcm_recursive(a: int, b: int) -> (result: int)
    requires a >= 0,
             b >= 0
{
    if a == 0 || b == 0 {
        0
    } else {
        let common_divisor = gcd(a, b);
        if common_divisor == 0 {
            // This case should not happen if a, b > 0
            0
        } else {
            (a / common_divisor) * b
        }
    }
}
// </vc-helpers>

// <vc-spec>
spec fn gcd_spec(a: int, b: int) -> nat;

spec fn lcm_spec(a: int, b: int) -> nat;

fn lcm(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),

        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,

        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,

        forall|i: int| 0 <= i < result.len() ==> 
            (x1[i] == 0 || x2[i] == 0) ==> result[i] == 0,

        forall|i: int| 0 <= i < result.len() ==> 
            (x1[i] != 0 && x2[i] != 0) ==> result[i] > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type casting within the loop condition to use `usize` consistently for vector access, removed unnecessary `as int` casts for `lcm_recursive` arguments, and ensured `current_lcm` is handled as `int` before `as i32`. */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            0 <= i && i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> result[j] >= 0,
            forall|j: int| 0 <= j < (i as int) ==> (x1[j as usize] == 0 || x2[j as usize] == 0) ==> result[j] == 0,
            forall|j: int| 0 <= j < (i as int) ==> (x1[j as usize] != 0 && x2[j as usize] != 0) ==> result[j] > 0
    {
        let val_a: int = x1[i] as int;
        let val_b: int = x2[i] as int;
        let current_lcm: int = lcm_recursive(val_a, val_b);
        result.push(current_lcm as i32);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}