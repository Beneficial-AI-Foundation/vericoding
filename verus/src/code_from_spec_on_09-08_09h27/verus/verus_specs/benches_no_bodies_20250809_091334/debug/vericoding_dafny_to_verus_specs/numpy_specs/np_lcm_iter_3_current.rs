use vstd::prelude::*;

verus! {

// Helper function to compute GCD of two integers
spec fn gcd_int(a: int, b: int) -> int 
    decreases (if a >= 0 { a } else { -a }) + (if b >= 0 { b } else { -b })
{
    if a == 0 {
        if b >= 0 { b } else { -b }
    } else if b == 0 {
        if a >= 0 { a } else { -a }
    } else if a >= 0 && b >= 0 {
        if a >= b {
            gcd_int(a - b, b)
        } else {
            gcd_int(a, b - a)
        }
    } else if a >= 0 && b < 0 {
        gcd_int(a, -b)
    } else if a < 0 && b >= 0 {
        gcd_int(-a, b)
    } else {
        gcd_int(-a, -b)
    }
}

// Helper function to compute LCM of two integers (uninterpreted specification function)
#[verifier::external_body]
spec fn lcm_int(a: int, b: int) -> int {
    if a == 0 || b == 0 {
        0
    } else {
        let abs_a = if a >= 0 { a } else { -a };
        let abs_b = if b >= 0 { b } else { -b };
        (abs_a * abs_b) / gcd_int(abs_a, abs_b)
    }
}

// Runtime GCD implementation
fn gcd_runtime(mut a: i32, mut b: i32) -> (res: i32)
    requires a >= 0 && b >= 0
    ensures res >= 0
    ensures res == gcd_int(a as int, b as int)
{
    /* code modified by LLM (iteration 1): added missing curly braces and fixed function body */
    while a != 0 && b != 0
        invariant a >= 0 && b >= 0
        invariant gcd_int(a as int, b as int) == gcd_int(old(a) as int, old(b) as int)
    {
        if a >= b {
            a = a - b;
        } else {
            b = b - a;
        }
    }
    if a == 0 { b } else { a }
}

// Runtime LCM implementation for two non-negative integers
fn lcm_runtime(a: i32, b: i32) -> (res: i32)
    requires a >= 0 && b >= 0
    ensures res >= 0
    ensures res == lcm_int(a as int, b as int)
{
    /* code modified by LLM (iteration 1): implemented LCM function body */
    if a == 0 || b == 0 {
        0
    } else {
        let g = gcd_runtime(a, b);
        (a / g) * b
    }
}

// Method specification (translation of the Dafny method)
fn lcm(a: &[i32], b: &[i32]) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] >= 0 && b[i] >= 0,
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> lcm_int(a[i] as int, b[i] as int) == res[i] as int,
{
    /* code modified by LLM (iteration 1): implemented LCM array function body */
    let mut result = Vec::new();
    let mut idx = 0;
    
    while idx < a.len()
        invariant 
            idx <= a.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> lcm_int(a[i] as int, b[i] as int) == result[i] as int,
    {
        let lcm_val = lcm_runtime(a[idx], b[idx]);
        result.push(lcm_val);
        idx += 1;
    }
    
    result
}

}

fn main() {}