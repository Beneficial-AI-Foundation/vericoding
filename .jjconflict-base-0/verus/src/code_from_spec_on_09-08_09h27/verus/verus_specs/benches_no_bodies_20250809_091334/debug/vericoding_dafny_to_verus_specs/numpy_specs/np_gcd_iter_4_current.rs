use vstd::prelude::*;

verus! {

// Helper function to compute GCD of two integers - uninterpreted like in Dafny
#[verifier::external_body]
spec fn gcd_int(a: int, b: int) -> int {
    unimplemented!()
}

// Helper function to compute GCD using Euclidean algorithm
fn compute_gcd(mut a: i32, mut b: i32) -> (result: i32)
    requires a >= 0, b >= 0
    ensures result >= 0
    ensures result == gcd_int(a as int, b as int)
{
    /* code modified by LLM (iteration 1): fixed function syntax and added missing braces */
    if a == 0 {
        return b;
    }
    if b == 0 {
        return a;
    }
    
    while b != 0
        invariant a >= 0, b >= 0
        invariant gcd_int(a as int, b as int) == gcd_int(old(a) as int, old(b) as int)
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
    ensures res.len() == a.len()
    ensures forall|i: int| 0 <= i < a.len() ==> gcd_int(a@[i] as int, b@[i] as int) == res@[i] as int
{
    /* code modified by LLM (iteration 1): fixed function syntax and vector operations */
    let mut result = Vec::new();
    let mut index = 0;
    
    while index < a.len()
        invariant 
            index <= a.len(),
            result.len() == index,
            forall|i: int| 0 <= i < index ==> gcd_int(a@[i] as int, b@[i] as int) == result@[i] as int
    {
        let gcd_val = compute_gcd(a[index], b[index]);
        result.push(gcd_val);
        index += 1;
    }
    
    result
}

}

fn main() {}