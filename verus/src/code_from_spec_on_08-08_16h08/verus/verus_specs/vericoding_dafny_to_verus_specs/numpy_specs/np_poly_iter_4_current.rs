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
        /* code modified by LLM (iteration 1): replaced fold with manual sequence construction */
        let mut result = seq![0];
        let result = result + prev;
        let mut final_result = result;
        let mut i: int = 1;
        while i < final_result.len()
            invariant
                1 <= i <= final_result.len(),
                final_result.len() == prev.len() + 1,
            decreases final_result.len() - i
        {
            final_result = final_result.update((i - 1) as int, final_result[(i - 1) as int] - root * final_result[i as int]);
            i = i + 1;
        }
        final_result
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
        val < roots.len()
    ensures 
        coeff.len() == roots.len(),
        coeff.len() > 0 ==> coeff[0] == 1
{
    if val == 0 {
        /* code modified by LLM (iteration 2): fixed base case with proper int types */
        let mut result: Vec<int> = Vec::new();
        result.push(1int);
        while result.len() < roots.len()
            invariant 
                result.len() >= 1,
                result.len() <= roots.len(),
                result[0] == 1
        {
            result.push(0int);
        }
        return result;
    }
    
    let prev = poly_helper_method(roots, val - 1);
    let root = roots[val];
    let mut result: Vec<int> = Vec::new();
    
    /* code modified by LLM (iteration 2): fixed type annotations and arithmetic operations */
    // Shift coefficients (multiply by x)
    result.push(0int);
    let mut i: usize = 0;
    while i < prev.len()
        invariant
            i <= prev.len(),
            result.len() == i + 1
    {
        result.push(prev[i]);
        i = i + 1;
    }
    
    // Subtract root * prev (multiply by -root and add)
    let mut j: usize = 1;
    while j < result.len()
        invariant
            1 <= j <= result.len(),
            result.len() == prev.len() + 1
    {
        let old_val: int = result[j - 1];
        let subtract_val: int = root * result[j];
        result.set(j - 1, old_val - subtract_val);
        j = j + 1;
    }
    
    // Trim to original size
    while result.len() > roots.len()
        invariant result.len() >= roots.len()
    {
        result.pop();
    }
    
    result
}

}

fn main() {}