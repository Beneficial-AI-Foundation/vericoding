use vstd::prelude::*;

verus! {

// Helper function to compute GCD of two integers
spec fn gcd_int(a: int, b: int) -> int
    decreases a.abs() + b.abs()
{
    if b == 0 {
        a.abs()
    } else {
        gcd_int(b, a % b)
    }
}

// Helper function to compute LCM of two integers (uninterpreted specification function)
#[verifier::external_body]
spec fn lcm_int(a: int, b: int) -> int {
    if a == 0 && b == 0 {
        0
    } else {
        (a * b).abs() / gcd_int(a, b)
    }
}

// Concrete GCD implementation
fn gcd(a: i32, b: i32) -> (res: i32)
    requires a >= 0, b >= 0
    ensures res >= 0
{
    let mut x = a;
    let mut y = b;
    
    while y != 0
        invariant x >= 0, y >= 0
    {
        let temp = y;
        y = x % y;
        x = temp;
    }
    x
}

// Concrete LCM implementation for two numbers
fn lcm_pair(a: i32, b: i32) -> (res: i32)
    requires a >= 0, b >= 0
    ensures res >= 0
    ensures res as int == lcm_int(a as int, b as int)
{
    /* code modified by LLM (iteration 1): added missing curly braces for function body */
    if a == 0 && b == 0 {
        0
    } else {
        let g = gcd(a, b);
        if g == 0 {
            0
        } else {
            (a / g) * b
        }
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
    let mut result = Vec::new();
    
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> lcm_int(a[j] as int, b[j] as int) == result[j] as int,
    {
        let lcm_val = lcm_pair(a[i], b[i]);
        result.push(lcm_val);
    }
    
    result
}

}

fn main() {}