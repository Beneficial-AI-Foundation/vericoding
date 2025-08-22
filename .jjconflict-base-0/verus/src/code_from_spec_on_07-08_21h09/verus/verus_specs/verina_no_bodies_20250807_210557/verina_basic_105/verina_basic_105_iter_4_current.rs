use vstd::prelude::*;

verus! {

// Precondition: arrays must have the same size
spec fn array_product_precond(a: Seq<i32>, b: Seq<i32>) -> bool {
    a.len() == b.len()
}

// Postcondition: result has same size and contains element-wise products
spec fn array_product_postcond(a: Seq<i32>, b: Seq<i32>, result: Seq<i32>) -> bool {
    result.len() == a.len() &&
    forall|i: int| #![trigger result[i], a[i], b[i]] 0 <= i < a.len() ==> result[i] == a[i] * b[i]
}

// Helper recursive loop function matching the original Lean structure
fn array_loop(a: &Vec<i32>, b: &Vec<i32>, len: usize, i: usize, c: &mut Vec<i32>)
    requires
        a.len() == b.len(),
        len == a.len(),
        i <= len,
        old(c).len() == len,
        forall|j: int| #![trigger old(c)[j], a@[j], b@[j]] 0 <= j < i ==> old(c)[j] == a@[j] * b@[j]
    ensures
        c.len() == len,
        forall|j: int| #![trigger c[j], a@[j], b@[j]] 0 <= j < len ==> c[j] == a@[j] * b@[j]
    decreases len - i
{
    if i < len {
        c.set(i, a[i] * b[i]);
        array_loop(a, b, len, i + 1, c);
    }
}

// Main function
fn array_product(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires array_product_precond(a@, b@)
    ensures array_product_postcond(a@, b@, result@)
{
    let mut result = Vec::with_capacity(a.len());
    let len = a.len();
    
    // Initialize the vector with zeros
    let mut i = 0;
    while i < len
        invariant 
            result.len() == i,
            i <= len,
            len == a.len()
    {
        result.push(0);
        i = i + 1;
    }
    
    // Fill the vector with products
    array_loop(a, b, len, 0, &mut result);
    result
}

// Specification theorem - represents that the specification is satisfied
proof fn array_product_spec_satisfied(a: Seq<i32>, b: Seq<i32>)
    requires array_product_precond(a, b)
    ensures 
        exists|result: Seq<i32>| array_product_postcond(a, b, result)
{
    /* code modified by LLM (iteration 1): Fixed type mismatch by constructing result sequence element by element with proper i32 types */
    // We construct the result by showing it exists through the actual computation
    let ghost result = a.zip_with(b, |x: i32, y: i32| x * y);
    
    // Show that this result satisfies the postcondition
    assert(result.len() == a.len());
    assert(forall|i: int| #![trigger result[i], a[i], b[i]] 0 <= i < a.len() ==> result[i] == a[i] * b[i]) by {
        assert forall|i: int| #![trigger result[i], a[i], b[i]] 0 <= i < a.len() implies result[i] == a[i] * b[i] by {
            // This follows from the definition of zip_with
        }
    }
    
    assert(array_product_postcond(a, b, result));
}

}

fn main() {}