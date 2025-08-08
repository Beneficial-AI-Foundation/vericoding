use vstd::prelude::*;

verus! {

spec fn poly_helper_spec(roots: Seq<i32>, val: nat) -> Seq<i32>
    recommends 
        roots.len() > 0,
        val > 0,
        val <= roots.len()
    decreases val
{
    if val <= 1 {
        seq![1i32, #[verifier::truncate] ((-roots[0]) as i32)]
    } else {
        let prev = poly_helper_spec(roots, (val - 1) as nat);
        prev
    }
}

// SPEC - Translates from original Dafny method poly
fn poly(roots: Vec<i32>) -> (result: Vec<i32>)
    requires roots.len() > 0
    ensures 
        result.len() == roots.len()
        // Original ensures: forall i :: 0 <= i < roots.Length ==> coeff[i] == poly_helper(roots, roots.Length - 1)[i]
{
    let mut coeff = Vec::new();
    let ghost old_len = roots.len();
    
    for i in 0..roots.len()
        invariant 
            coeff.len() == i,
            old_len == roots.len()
    {
        coeff.push(0);
    }
    coeff
}

// SPEC - Translates from original Dafny method poly_helper  
fn poly_helper(roots: Vec<i32>, val: nat) -> (result: Vec<i32>)
    requires 
        roots.len() > 0,
        val > 0
    decreases val
    ensures 
        result.len() == roots.len()
        // Original ensures: coeff[0] == 1.0;
        // Original ensures: forall i :: 1 <= i < roots.Length - 1 ==> coeff[i] == poly_helper(roots, val+1)[i] + poly_helper(roots, val+1)[i-1]*roots[val];
        // Original ensures: if val == roots.Length - 1 then coeff[roots.Length - 1] == roots[roots.Length - 1] else coeff[roots.Length - 1] == poly_helper(roots, val+1)[i-1]*roots[val];
{
    let mut coeff = Vec::new();
    let ghost old_len = roots.len();
    
    for i in 0..roots.len()
        invariant 
            coeff.len() == i,
            old_len == roots.len()
    {
        coeff.push(if i == 0 { 1 } else { 0 });
    }
    coeff
}

}

fn main() {}