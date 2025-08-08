use vstd::prelude::*;

verus! {

// Helper function to compute GCD using Euclidean algorithm
spec fn gcd_int(a: int, b: int) -> int
    decreases a, b
{
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else if a <= b {
        gcd_int(a, b % a)
    } else {
        gcd_int(a % b, b)
    }
}

// Helper function to compute LCM of two integers (uninterpreted specification function)
#[verifier::external_body]
spec fn lcm_int(a: int, b: int) -> int {
    if a == 0 || b == 0 {
        0
    } else {
        (a * b) / gcd_int(a, b)
    }
}

// Runtime GCD implementation
fn gcd_runtime(a: i32, b: i32) -> (res: i32)
    requires a >= 0, b >= 0
    ensures res >= 0
    ensures res as int == gcd_int(a as int, b as int)
{
    /* code modified by LLM (iteration 1): added missing opening curly brace and implemented function body */
    let mut x = a;
    let mut y = b;
    
    while y != 0
        invariant x >= 0, y >= 0
        invariant gcd_int(x as int, y as int) == gcd_int(a as int, b as int)
    {
        let temp = y;
        y = x % y;
        x = temp;
    }
    x
}

// Runtime LCM implementation
fn lcm_runtime(a: i32, b: i32) -> (res: i32)
    requires a >= 0, b >= 0
    ensures res >= 0
    ensures res as int == lcm_int(a as int, b as int)
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
    /* code modified by LLM (iteration 1): implemented array LCM function body */
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