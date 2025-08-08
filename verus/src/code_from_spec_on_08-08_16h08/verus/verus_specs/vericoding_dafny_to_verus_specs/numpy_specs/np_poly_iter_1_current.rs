use vstd::prelude::*;

verus! {

spec fn poly_helper(roots: Seq<int>, val: nat) -> Seq<int>
    decreases val
{
    if val == 0 {
        seq![1]
    } else if val >= roots.len() {
        seq![1]
    } else {
        let prev = poly_helper(roots, (val - 1) as nat);
        let root = roots[val as int];
        let mut result = Seq::<int>::empty();
        let result = result.push(0);
        let result = (0..prev.len()).fold(result, |acc: Seq<int>, i: int| {
            acc.update(i + 1, prev[i])
        });
        (0..result.len()).fold(result, |acc: Seq<int>, i: int| {
            if i > 0 {
                acc.update(i - 1, acc[i - 1] - root * acc[i])
            } else {
                acc
            }
        })
    }
}

// SPEC function - equivalent to Dafny's poly method
spec fn poly(roots: Seq<int>) -> Seq<int>
    recommends roots.len() > 0
{
    poly_helper(roots, (roots.len() - 1) as nat)
}

// SPEC function - equivalent to Dafny's poly_helper method  
spec fn poly_helper_spec(roots: Seq<int>, val: nat) -> Seq<int>
    recommends 
        roots.len() > 0,
        val > 0
    decreases val
{
    poly_helper(roots, val)
}

// Executable methods with specifications
fn poly_method(roots: Vec<int>) -> (coeff: Vec<int>)
    requires roots.len() > 0
    ensures 
        coeff.len() == roots.len(),
        forall|i: int| 0 <= i < roots.len() ==> coeff[i] == poly(roots@)[i]
{
    poly_helper_method(roots, roots.len() - 1)
}

fn poly_helper_method(roots: Vec<int>, val: usize) -> (coeff: Vec<int>)
    requires 
        roots.len() > 0,
        val > 0
    ensures 
        coeff.len() == roots.len(),
        coeff.len() > 0 ==> coeff[0] == 1
{
    if val == 0 || val >= roots.len() {
        let mut result = Vec::new();
        result.push(1);
        while result.len() < roots.len() {
            result.push(0);
        }
        return result;
    }
    
    let prev = poly_helper_method(roots, val - 1);
    let root = roots[val];
    let mut result = Vec::new();
    
    // Shift coefficients (multiply by x)
    result.push(0);
    for i in 0..prev.len() {
        result.push(prev[i]);
    }
    
    // Subtract root * prev (multiply by -root and add)
    for i in 1..result.len() {
        result.set(i - 1, result[i - 1] - root * result[i]);
    }
    
    // Trim to original size
    while result.len() > roots.len() {
        result.pop();
    }
    
    result
}

}

fn main() {}