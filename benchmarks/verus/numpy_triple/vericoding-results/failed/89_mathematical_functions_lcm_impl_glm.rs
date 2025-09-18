// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): removed spec functions to avoid duplicates and kept only executable functions */
fn gcd_exec_nonnegative(a: u32, b: u32) -> u32
    decreases b
{
    if b == 0 {
        a
    } else {
        gcd_exec_nonnegative(b, a % b)
    }
}

fn gcd_exec(a: i32, b: i32) -> i32 {
    let a_abs = if a < 0 { -a } else { a };
    let b_abs = if b < 0 { -b } else { b };
    gcd_exec_nonnegative(a_abs as u32, b_abs as u32) as i32
}

fn lcm_exec(a: i32, b: i32) -> i32 {
    if a == 0 || b == 0 {
        0
    } else {
        let a_abs = if a < 0 { -a } else { a };
        let b_abs = if b < 0 { -b } else { b };
        let g = gcd_exec(a, b);
        (a_abs / g) * b_abs
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
{
    /* code modified by LLM (iteration 5): fixed type annotation for result vector */
    let mut result: Vec<i32> = Vec::with_capacity(x1.len());
    for i in 0..x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                (x1[j] == 0 || x2[j] == 0) ==> result[j] == 0,
            forall|j: int| 0 <= j < i ==> 
                (x1[j] != 0 && x2[j] != 0) ==> result[j] > 0,
            forall|j: int| 0 <= j < i ==> result[j] >= 0,
    {
        let a = x1[i];
        let b = x2[i];
        let lcm_val = lcm_exec(a, b);
        result.push(lcm_val);
    }
    result
}
// </vc-code>

}
fn main() {}