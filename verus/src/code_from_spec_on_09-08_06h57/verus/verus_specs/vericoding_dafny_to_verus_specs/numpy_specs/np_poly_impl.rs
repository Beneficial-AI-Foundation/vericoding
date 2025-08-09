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
        // Multiply prev by (x - root)
        // prev[i] * x gives coefficient at position i+1
        // prev[i] * (-root) gives coefficient at position i
        result = result.push(prev[0] * (-root));
        /* code modified by LLM (iteration 1): added explicit type annotation for i */
        let mut i: int = 1;
        while i < prev.len()
            invariant
                0 < i <= prev.len(),
                result.len() == i
        {
            let coeff = prev[i] * (-root) + prev[i-1];
            result = result.push(coeff);
            i = i + 1;
        }
        result.push(prev[prev.len()-1])
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
    /* code modified by LLM (iteration 2): fix invalid int literal syntax */
    let mut result: Vec<int> = Vec::new();
    result.push(1);
    
    let mut k: usize = 0;
    while k < roots.len()
        invariant
            0 <= k <= roots.len(),
            result.len() == k + 1,
            result.len() > 0
    {
        let root = roots[k];
        let mut new_result: Vec<int> = Vec::new();
        
        // First coefficient: result[0] * (-root)
        new_result.push(result[0] * (-root));
        
        // Middle coefficients: result[i] * (-root) + result[i-1]
        let mut i: usize = 1;
        while i < result.len()
            invariant
                1 <= i <= result.len(),
                new_result.len() == i,
                result.len() > 0
        {
            let coeff = result[i] * (-root) + result[i-1];
            new_result.push(coeff);
            i = i + 1;
        }
        
        // Last coefficient: result[result.len()-1]
        new_result.push(result[result.len()-1]);
        
        result = new_result;
        k = k + 1;
    }
    
    result
}

fn poly_helper_method(roots: Vec<int>, val: usize) -> (coeff: Vec<int>)
    requires 
        roots.len() > 0,
        val > 0
    ensures 
        coeff.len() == roots.len(),
        coeff.len() > 0 ==> coeff[0] == 1
{
    /* code modified by LLM (iteration 2): fix invalid int literal syntax */
    let mut result: Vec<int> = Vec::new();
    result.push(1);
    
    let end_val = if val >= roots.len() { roots.len() } else { val };
    
    let mut k: usize = 0;
    while k < end_val
        invariant
            0 <= k <= end_val,
            end_val <= roots.len(),
            result.len() == k + 1,
            result.len() > 0,
            result[0] == 1
    {
        let root = roots[k];
        let mut new_result: Vec<int> = Vec::new();
        
        // First coefficient: result[0] * (-root) = 1 * (-root) = -root
        new_result.push(result[0] * (-root));
        
        // Middle coefficients
        let mut i: usize = 1;
        while i < result.len()
            invariant
                1 <= i <= result.len(),
                new_result.len() == i,
                result.len() > 0
        {
            let coeff = result[i] * (-root) + result[i-1];
            new_result.push(coeff);
            i = i + 1;
        }
        
        // Last coefficient: result[result.len()-1]
        new_result.push(result[result.len()-1]);
        
        result = new_result;
        k = k + 1;
    }
    
    // Pad with zeros if needed to match roots.len()
    while result.len() < roots.len()
        invariant
            result.len() <= roots.len(),
            result.len() > 0,
            result[0] == 1
    {
        /* code modified by LLM (iteration 2): fix invalid int literal syntax */
        result.push(0);
    }
    
    result
}

}

fn main() {}