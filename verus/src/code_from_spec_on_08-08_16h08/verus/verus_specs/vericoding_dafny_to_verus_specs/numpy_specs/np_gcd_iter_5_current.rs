use vstd::prelude::*;

verus! {

// Helper function to compute GCD of two integers - uninterpreted like in Dafny
#[verifier::external_body]
spec fn gcd_int(a: int, b: int) -> int {
    unimplemented!()
}

// Helper function to compute GCD using Euclid's algorithm
fn compute_gcd(mut a: i32, mut b: i32) -> (res: i32)
    requires a >= 0, b >= 0
    ensures res >= 0
    ensures res == gcd_int(old(a) as int, old(b) as int)
    decreases b
/* code modified by LLM (iteration 4): fixed function specification syntax and added proper braces */
{
    while b != 0
        invariant a >= 0, b >= 0
        invariant gcd_int(a as int, b as int) == gcd_int(old(a) as int, old(b) as int)
        decreases b
    {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

// Method signature matching the original Dafny specification
fn gcd(a: &Vec<i32>, b: &Vec<i32>) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> a@[i] >= 0 && b@[i] >= 0
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> gcd_int(a@[i] as int, b@[i] as int) == res@[i] as int
/* code modified by LLM (iteration 4): implemented function body with proper loop invariants */
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant 
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> gcd_int(a@[j] as int, b@[j] as int) == result@[j] as int
    {
        let gcd_val = compute_gcd(a@[i], b@[i]);
        result.push(gcd_val);
        i += 1;
    }
    
    result
}

}

fn main() {}