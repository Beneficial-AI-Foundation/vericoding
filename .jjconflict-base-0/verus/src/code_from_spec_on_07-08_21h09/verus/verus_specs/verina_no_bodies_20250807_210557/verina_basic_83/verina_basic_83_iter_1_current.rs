use vstd::prelude::*;

verus! {

// Precondition for concat - currently just True (like in Lean)
spec fn concat_precond(a: &Vec<i32>, b: &Vec<i32>) -> bool {
    true
}

// Postcondition for concat  
spec fn concat_postcond(a: &Vec<i32>, b: &Vec<i32>, result: &Vec<i32>) -> bool {
    result.len() == a.len() + b.len()
    && (forall|k: int| 0 <= k < a.len() ==> result[k] == a[k])
    && (forall|k: int| 0 <= k < b.len() ==> result[k + a.len()] == b[k])
}

// The concat function implementation
fn concat(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires 
        concat_precond(a, b),
        a.len() + b.len() <= usize::MAX,
    ensures concat_postcond(a, b, &result),
{
    let mut result = Vec::new();
    
    // Add all elements from vector a
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == a[k],
    {
        result.push(a[i]);
        i += 1;
    }
    
    // Add all elements from vector b
    let mut j = 0;
    while j < b.len()
        invariant
            j <= b.len(),
            result.len() == a.len() + j,
            forall|k: int| 0 <= k < a.len() ==> result[k] == a[k],
            forall|k: int| 0 <= k < j ==> result[k + a.len()] == b[k],
    {
        result.push(b[j]);
        j += 1;
    }
    
    result
}

}

fn main() {}