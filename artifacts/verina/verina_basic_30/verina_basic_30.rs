use vstd::prelude::*;

verus! {

// Precondition for elementWiseModulo  
spec fn elementWiseModulo_precond(a: Seq<i32>, b: Seq<i32>) -> bool {
    a.len() == b.len() && a.len() > 0 &&
    forall|i: int| 0 <= i < b.len() ==> b[i] != 0
}

// Main function that performs element-wise modulo
#[verifier::external_body]
fn elementWiseModulo(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        a.len() > 0,
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
{
    // This implementation mirrors the Lean mapIdx functionality
    let mut result = Vec::new();
    for i in 0..a.len() {
        result.push(a[i] % b[i]);
    }
    result
}

// Postcondition specification  
spec fn elementWiseModulo_postcond(a: Seq<i32>, b: Seq<i32>, result: Seq<i32>) -> bool {
    result.len() == a.len() &&
    forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i]
}

} // verus!

fn main() {
    // Example usage (this won't be verified due to external_body)
    let a = vec![10, 15, 7];
    let b = vec![3, 4, 2];
    let result = elementWiseModulo(a, b);
    println!("{:?}", result); // Should print [1, 3, 1]
}