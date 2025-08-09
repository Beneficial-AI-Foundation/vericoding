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

/* code modified by LLM (iteration 3): fixed borrow checker issue by storing value in temporary variable */
fn sort_vec(vec: &mut Vec<i32>)
    ensures vec@.len() == old(vec)@.len(),
            forall|i: int, j: int| 0 <= i < j < vec@.len() ==> vec@[i] <= vec@[j],
            forall|x: i32| old(vec)@.contains(x) == vec@.contains(x)
{
    let len = vec.len();
    for i in 1..len
        invariant 
            vec@.len() == old(vec)@.len(),
            forall|k: int, l: int| 0 <= k < l < i ==> vec@[k] <= vec@[l],
            forall|x: i32| old(vec)@.contains(x) == vec@.contains(x)
    {
        let key = vec[i];
        let mut j = i;
        
        while j > 0 && vec[j - 1] > key
            invariant 
                0 <= j <= i,
                vec@.len() == old(vec)@.len(),
                forall|x: i32| old(vec)@.contains(x) == vec@.contains(x),
                forall|k: int| j < k <= i ==> vec@[k] == key,
                forall|k: int, l: int| 0 <= k < l < j ==> vec@[k] <= vec@[l],
                forall|k: int, l: int| i < k < l < vec@.len() ==> vec@[k] <= vec@[l]
        {
            let temp = vec[j - 1];
            vec.set(j, temp);
            j = j - 1;
        }
        vec.set(j, key);
    }
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
            forall|j: int| 0 <= j < i ==> (b@.contains(a@[j]) || result@.contains(a@[j])),
    {
        if !in_array(b, a[i]) && !contains_element(&result, a[i]) {
            result.push(a[i]);
        }
    }
    
    // Add elements from b that are not in a
    for i in 0..b.len()
        invariant 
            forall|x: i32| result@.contains(x) ==> ((a@.contains(x) && !b@.contains(x)) || (b@.contains(x) && !a@.contains(x))),
            forall|j: int| 0 <= j < i ==> (a@.contains(b@[j]) || result@.contains(b@[j])),
            forall|x: i32| a@.contains(x) && !b@.contains(x) ==> result@.contains(x),
    {
        if !in_array(a, b[i]) && !contains_element(&result, b[i]) {
            result.push(b[i]);
        }
    }
    
    /* code modified by LLM (iteration 1): replaced unsupported sort() with manual sort_vec function */
    sort_vec(&mut result);
    
    result
}

fn main() {}

} // verus!