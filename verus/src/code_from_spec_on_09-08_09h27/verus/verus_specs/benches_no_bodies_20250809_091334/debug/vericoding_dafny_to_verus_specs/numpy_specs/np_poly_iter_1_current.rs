use vstd::prelude::*;

verus! {

spec fn poly_helper(roots: Seq<int>, val: nat) -> Seq<int>
    decreases val
{
    if val == 0 {
        seq![1int]
    } else if val >= roots.len() {
        seq![1int]
    } else {
        let prev = poly_helper(roots, val - 1);
        let root = roots[val as int];
        let mut result = seq![0int; (val + 1) as nat];
        let result = result.update(0, -root * prev[0]);
        let result = seq![0int; (val + 1) as nat].update(0, -root * prev[0]);
        // For i from 1 to val, result[i] = prev[i-1] - root * prev[i]
        (0..=val).fold(result, |acc, i| {
            if i == 0 {
                acc.update(i as int, -root * prev[0])
            } else if i as int < prev.len() {
                acc.update(i as int, prev[(i-1) as int] - root * prev[i as int])
            } else {
                acc.update(i as int, prev[(i-1) as int])
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
    let mut coeff = vec![1int];
    
    let mut j = 0;
    while j < roots.len()
        invariant
            j <= roots.len(),
            coeff.len() == j + 1,
            coeff.len() > 0,
            coeff@ == poly_helper(roots@, j as nat)
    {
        let root = roots[j];
        let mut new_coeff = vec![0int; coeff.len() + 1];
        
        // new_coeff[0] = -root * coeff[0]
        new_coeff.set(0, -root * coeff[0]);
        
        let mut i = 1;
        while i < coeff.len()
            invariant
                1 <= i <= coeff.len(),
                new_coeff.len() == coeff.len() + 1,
                new_coeff[0] == -root * coeff[0],
                forall|k: int| 1 <= k < i ==> new_coeff[k] == coeff[k-1] - root * coeff[k]
        {
            new_coeff.set(i, coeff[i-1] - root * coeff[i]);
            i += 1;
        }
        
        // new_coeff[coeff.len()] = coeff[coeff.len()-1]
        new_coeff.set(coeff.len(), coeff[coeff.len()-1]);
        
        coeff = new_coeff;
        j += 1;
    }
    
    coeff
}

fn poly_helper_method(roots: Vec<int>, val: usize) -> (coeff: Vec<int>)
    requires 
        roots.len() > 0,
        val > 0
    ensures 
        coeff.len() == roots.len(),
        coeff.len() > 0 ==> coeff[0] == 1
{
    if val >= roots.len() {
        let mut result = vec![0int; roots.len()];
        result.set(0, 1);
        return result;
    }
    
    let mut coeff = vec![1int];
    
    let mut j = 0;
    while j <= val
        invariant
            j <= val + 1,
            j <= roots.len(),
            coeff.len() == j + 1,
            coeff.len() > 0
    {
        if j == val + 1 {
            break;
        }
        
        let root = roots[j];
        let mut new_coeff = vec![0int; coeff.len() + 1];
        
        new_coeff.set(0, -root * coeff[0]);
        
        let mut i = 1;
        while i < coeff.len()
            invariant
                1 <= i <= coeff.len(),
                new_coeff.len() == coeff.len() + 1
        {
            new_coeff.set(i, coeff[i-1] - root * coeff[i]);
            i += 1;
        }
        
        new_coeff.set(coeff.len(), coeff[coeff.len()-1]);
        coeff = new_coeff;
        j += 1;
    }
    
    // Pad or truncate to match roots.len()
    let mut result = vec![0int; roots.len()];
    result.set(0, 1);
    
    let mut i = 0;
    while i < coeff.len() && i < roots.len()
        invariant
            i <= coeff.len(),
            i <= roots.len(),
            result.len() == roots.len(),
            result[0] == 1
    {
        if i == 0 {
            result.set(0, 1);
        } else {
            result.set(i, coeff[i]);
        }
        i += 1;
    }
    
    result
}

}

fn main() {}