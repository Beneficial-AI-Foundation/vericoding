// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Added decreases clause to both loops */
    let mut result: Vec<i32> = Vec::new();
    let n = x1.len();
    
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] >= 0,
            forall|j: int| 0 <= j < i ==> (x1[j] == 0 || x2[j] == 0) ==> result[j] == 0,
            forall|j: int| 0 <= j < i ==> (x1[j] != 0 && x2[j] != 0) ==> result[j] > 0,
        decreases n - i
    {
        let a = x1[i];
        let b = x2[i];
        
        if a == 0 || b == 0 {
            result.push(0);
        } else {
            let abs_a = if a >= 0 { a } else { -a };
            let abs_b = if b >= 0 { b } else { -b };
            
            // Compute GCD using Euclidean algorithm
            let mut gcd_a = abs_a;
            let mut gcd_b = abs_b;
            while gcd_b != 0
                invariant
                    gcd_a >= 0,
                    gcd_b >= 0,
                decreases gcd_b
            {
                let temp = gcd_b;
                gcd_b = gcd_a % gcd_b;
                gcd_a = temp;
            }
            
            // Compute LCM = (abs_a * abs_b) / gcd
            let lcm_val = (abs_a * abs_b) / gcd_a;
            result.push(lcm_val);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}