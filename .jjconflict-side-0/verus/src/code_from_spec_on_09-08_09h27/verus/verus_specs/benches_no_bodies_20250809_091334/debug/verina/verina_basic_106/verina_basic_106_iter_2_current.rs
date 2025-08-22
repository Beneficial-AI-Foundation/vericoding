use vstd::prelude::*;

verus! {

// Precondition: arrays must have the same size
spec fn arraysum_precond(a: &Vec<i32>, b: &Vec<i32>) -> bool {
    a.len() == b.len()
}

// Postcondition: result has same size and each element is sum of corresponding elements
spec fn arraysum_postcond(a: &Vec<i32>, b: &Vec<i32>, result: &Vec<i32>) -> bool {
    result.len() == a.len() &&
    forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i] == a[i] + b[i]
}

fn arraysum(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires arraysum_precond(a, b)
    ensures arraysum_postcond(a, b, &result)
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == a[j] + b[j]
        decreases a.len() - i
    {
        result.push(a[i] + b[i]);
        i += 1;
    }
    
    result
}

// The specification is automatically proven by Verus through the ensures clause
// and the loop invariants, corresponding to the "sorry" proof in the original Lean code

} // verus!

fn main() {}