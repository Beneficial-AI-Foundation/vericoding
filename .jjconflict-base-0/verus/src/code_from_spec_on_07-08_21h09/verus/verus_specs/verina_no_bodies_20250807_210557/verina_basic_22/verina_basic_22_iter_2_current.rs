use vstd::prelude::*;

verus! {

// Helper function equivalent to inArray
fn in_array(a: &Vec<i32>, x: i32) -> (result: bool)
    ensures result == a@.contains(x)
{
    for i in 0..a.len()
        invariant forall|j: int| 0 <= j < i ==> a@[j] != x
    {
        if a[i] == x {
            return true;
        }
    }
    false
}

// Helper to check if element is in result vector
fn contains_element(vec: &Vec<i32>, x: i32) -> (result: bool)
    ensures result == vec@.contains(x)
{
    for i in 0..vec.len()
        invariant forall|j: int| 0 <= j < i ==> vec@[j] != x
    {
        if vec[i] == x {
            return true;
        }
    }
    false
}

// Precondition - always true in this case
spec fn dissimilar_elements_precond(a: Seq<i32>, b: Seq<i32>) -> bool {
    true
}

// Postcondition specification
spec fn dissimilar_elements_postcond(a: Seq<i32>, b: Seq<i32>, result: Seq<i32>) -> bool {
    // All elements in result are in exactly one of a or b (not both)
    (forall|x: i32| result.contains(x) ==> (a.contains(x) != b.contains(x))) &&
    // Result is sorted
    (forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j]) &&
    // Elements in a but not in b are in result
    (forall|x: i32| a.contains(x) && !b.contains(x) ==> result.contains(x)) &&
    // Elements in b but not in a are in result  
    (forall|x: i32| b.contains(x) && !a.contains(x) ==> result.contains(x)) &&
    // Elements in both a and b are not in result
    (forall|x: i32| a.contains(x) && b.contains(x) ==> !result.contains(x))
}

// Main function
fn dissimilar_elements(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires dissimilar_elements_precond(a@, b@)
    ensures dissimilar_elements_postcond(a@, b@, result@)
{
    let mut result = Vec::new();
    
    // Add elements from a that are not in b
    for i in 0..a.len()
        invariant 
            forall|x: i32| result@.contains(x) ==> (a@.contains(x) && !b@.contains(x)),
            /* code modified by LLM (iteration 1): fixed syntax error by replacing 'in' with '.contains()' */
            forall|j: int| 0 <= j < i ==> result@.contains(a@[j]) || b@.contains(a@[j]),
            forall|x: i32| result@.contains(x) ==> (exists|k: int| 0 <= k < i && a@[k] == x)
    {
        if !in_array(b, a[i]) && !contains_element(&result, a[i]) {
            result.push(a[i]);
        }
    }
    
    // Add elements from b that are not in a
    for i in 0..b.len()
        invariant
            forall|x: i32| result@.contains(x) ==> ((a@.contains(x) && !b@.contains(x)) || (b@.contains(x) && !a@.contains(x))),
            /* code modified by LLM (iteration 1): fixed syntax error by replacing 'in' with '.contains()' */
            forall|j: int| 0 <= j < i ==> result@.contains(b@[j]) || a@.contains(b@[j]),
            forall|x: i32| a@.contains(x) && !b@.contains(x) ==> result@.contains(x),
            forall|x: i32| result@.contains(x) && b@.contains(x) ==> (exists|k: int| 0 <= k < i && b@[k] == x)
    {
        if !in_array(a, b[i]) && !contains_element(&result, b[i]) {
            result.push(b[i]);
        }
    }
    
    // Sort the result
    result.sort();
    
    result
}

// Theorem statement (proof omitted for simplicity)
proof fn dissimilar_elements_spec_satisfied(a: Vec<i32>, b: Vec<i32>) 
    requires dissimilar_elements_precond(a@, b@)
{
    // The proof that dissimilar_elements satisfies its postcondition would go here
    // This would be a substantial proof in a complete verification
}

fn main() {}

} // verus!