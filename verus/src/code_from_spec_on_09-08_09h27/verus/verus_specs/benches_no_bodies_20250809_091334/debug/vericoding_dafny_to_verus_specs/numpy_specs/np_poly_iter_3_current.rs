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
        /* code modified by LLM (iteration 1): fixed type issues and replaced fold with recursive approach */
        let prev = poly_helper(roots, (val - 1) as nat);
        let root = roots[val as int];
        
        // Build result sequence step by step
        let mut result = seq![0; (val + 1) as nat];
        result = result.update(0, -root * prev[0]);
        
        // Manually implement the fold logic
        poly_helper_build(prev, root, result, 1, val)
    }
}

spec fn poly_helper_build(prev: Seq<int>, root: int, acc: Seq<int>, i: nat, val: nat) -> Seq<int>
    decreases val + 1 - i
{
    if i > val {
        acc
    } else {
        let new_acc = if (i as int) < prev.len() {
            acc.update(i as int, prev[(i-1) as int] - root * prev[i as int])
        } else {
            acc.update(i as int, prev[(i-1) as int])
        };
        poly_helper_build(prev, root, new_acc, i + 1, val)
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
    /* code modified by LLM (iteration 1): fixed integer literal syntax */
    let mut coeff = vec![1];
    
    let mut j = 0;
    while j < roots.len()
        invariant
            j <= roots.len(),
            coeff.len() == j + 1,
            coeff.len() > 0,
            coeff@ == poly_helper(roots@, j as nat)
    {
        let root = roots[j];
        /* code modified by LLM (iteration 1): fixed integer literal syntax */
        let mut new_coeff = vec![0; coeff.len() + 1];
        
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
        /* code modified by LLM (iteration 1): fixed integer literal syntax */
        let mut result = vec![0; roots.len()];
        result.set(0, 1);
        return result;
    }
    
    /* code modified by LLM (iteration 1): fixed integer literal syntax */
    let mut coeff = vec![1];
    
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
        /* code modified by LLM (iteration 1): fixed integer literal syntax */
        let mut new_coeff = vec![0; coeff.len() + 1];
        
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
    /* code modified by LLM (iteration 1): fixed integer literal syntax */
    let mut result = vec![0; roots.len()];
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