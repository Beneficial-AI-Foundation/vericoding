// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added uninterp declarations and fixed Vec type annotation */
spec fn gcd_spec(a: int, b: int) -> nat by (uninterp);

spec fn lcm_spec(a: int, b: int) -> nat by (uninterp);

fn gcd(a: i32, b: i32) -> (result: i32)
    ensures result >= 0
{
    let mut x = if a < 0 { -a } else { a };
    let mut y = if b < 0 { -b } else { b };
    
    if x == 0 && y == 0 {
        return 1;
    }
    
    while y != 0
        invariant
            x >= 0,
            y >= 0
    {
        let temp = y;
        y = x % y;
        x = temp;
    }
    
    x
}

fn compute_lcm(a: i32, b: i32) -> (result: i32)
    ensures result >= 0,
            (a == 0 || b == 0) ==> result == 0,
            (a != 0 && b != 0) ==> result > 0
{
    if a == 0 || b == 0 {
        0
    } else {
        let abs_a = if a < 0 { -a } else { a };
        let abs_b = if b < 0 { -b } else { b };
        let gcd_val = gcd(a, b);
        (abs_a / gcd_val) * abs_b
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
    /* code modified by LLM (iteration 5): fixed Vec type annotation */
    let mut result: Vec<i32> = Vec::new();
    
    for i in 0..x1.len()
        invariant
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < result.len() ==> result[j] >= 0,
            forall|j: int| 0 <= j < result.len() ==> 
                (x1[j] == 0 || x2[j] == 0) ==> result[j] == 0,
            forall|j: int| 0 <= j < result.len() ==> 
                (x1[j] != 0 && x2[j] != 0) ==> result[j] > 0
    {
        let lcm_val = compute_lcm(x1[i], x2[i]);
        result.push(lcm_val);
    }
    
    result
}
// </vc-code>

}
fn main() {}