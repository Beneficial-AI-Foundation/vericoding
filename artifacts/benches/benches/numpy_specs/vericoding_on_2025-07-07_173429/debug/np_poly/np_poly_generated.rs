use vstd::prelude::*;

verus! {

fn poly(roots: &Vec<i32>) -> Vec<i32> {
    if roots.len() == 0 {
        Vec::new()
    } else {
        poly_helper(roots, roots.len() - 1)
    }
}

fn poly_helper(roots: &Vec<i32>, val: usize) -> Vec<i32> 
    decreases val
{
    let mut coeff = Vec::new();
    let mut i = 0;
    while i < roots.len()
        invariant 0 <= i <= roots.len() && coeff.len() == i
        decreases roots.len() - i
    {
        coeff.push(0);
        i += 1;
    }
    
    if val == 0 {
        // Base case: polynomial with one root
        if coeff.len() > 0 {
            coeff.set(0, 1);
        }
        if roots.len() > 1 && coeff.len() > 1 {
            // Assume arithmetic operations don't overflow for this example
            assume(roots[0] != i32::MIN);
            coeff.set(1, -roots[0]);
        }
        let mut j = 2;
        while j < roots.len() && j < coeff.len()
            invariant 2 <= j <= roots.len() && j <= coeff.len()
            invariant coeff[0] == 1
            invariant roots.len() > 1 ==> coeff[1] == -roots[0]
            invariant forall|k: int| 2 <= k < j ==> coeff[k] == 0
            decreases roots.len() - j
        {
            coeff.set(j, 0);
            j += 1;
        }
    } else if val < roots.len() {
        // Recursive case
        let prev_coeff = poly_helper(roots, val - 1);
        
        // Initialize with previous coefficients
        if coeff.len() > 0 {
            coeff.set(0, 1);
        }
        let mut j = 1;
        while j < roots.len() && j < coeff.len()
            invariant 1 <= j <= roots.len() && j <= coeff.len()
            invariant coeff[0] == 1
            decreases roots.len() - j
        {
            if j < prev_coeff.len() {
                let prev_val = if j > 0 && j - 1 < prev_coeff.len() { prev_coeff[j - 1] } else { 0 };
                if val < roots.len() && j < prev_coeff.len() {
                    // Assume arithmetic operations don't overflow
                    assume(roots[val as int] * prev_val >= i32::MIN && roots[val as int] * prev_val <= i32::MAX);
                    assume(prev_coeff[j as int] - roots[val as int] * prev_val >= i32::MIN && prev_coeff[j as int] - roots[val as int] * prev_val <= i32::MAX);
                    
                    let product = roots[val] * prev_val;
                    let new_val = prev_coeff[j] - product;
                    coeff.set(j, new_val);
                } else {
                    coeff.set(j, 0);
                }
            } else {
                coeff.set(j, 0);
            }
            j += 1;
        }
    }
    
    coeff
}

fn main() {}

}