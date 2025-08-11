use vstd::prelude::*;

verus! {

// Precondition for ToArray function
spec fn to_array_precond(xs: Seq<int>) -> bool {
    true
}

// Postcondition specification
spec fn to_array_postcond(xs: Seq<int>, result: Seq<int>) -> bool {
    result.len() == xs.len() && 
    (forall|i: int| 0 <= i < xs.len() ==> result[i] == xs[i])
}

// The ToArray function
fn to_array(xs: Vec<int>) -> (result: Vec<int>)
    requires to_array_precond(xs@),
    ensures to_array_postcond(xs@, result@),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < xs.len()
        invariant 
            0 <= i <= xs.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == xs@[j],
    {
        result.push(xs[i]);
        i += 1;
    }
    
    result
}

// Lemma that proves the specification is satisfied
proof fn to_array_spec_satisfied(xs: Seq<int>, result: Seq<int>)
    requires 
        to_array_precond(xs),
        result == xs,
    ensures to_array_postcond(xs, result),
{
    // Since result == xs, we have result.len() == xs.len()
    // and for all i, result[i] == xs[i] by definition of sequence equality
}

}

fn main() {}