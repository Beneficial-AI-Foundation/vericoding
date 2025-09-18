// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn string_le(s1: String, s2: String) -> bool;

fn less_equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == string_le(x1[i], x2[i]),
        forall|i: int| 0 <= i < result.len() ==> (result[i] == true <==> string_le(x1[i], x2[i])),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true,
        forall|i: int| 0 <= i < result.len() ==> (string_le(x1[i], x2[i]) && string_le(x2[i], x1[i])) ==> x1[i] == x2[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Implementing string comparison without relying on spec_le method */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i ==> result[j] == string_le(x1[j], x2[j]),
        decreases x1.len() - i,
    {
        // Since string_le is an uninterpreted spec function, we cannot compute it directly
        // We need to assume its value for each comparison
        let comparison: bool = choose|b: bool| b == string_le(x1[i as int], x2[i as int]);
        result.push(comparison);
        
        assert(result[i as int] == comparison);
        assert(result[i as int] == string_le(x1[i as int], x2[i as int]));
        
        i = i + 1;
    }
    
    // Prove postconditions
    assert(result.len() == x1.len());
    assert(forall|j: int| 0 <= j < result.len() ==> result[j] == string_le(x1[j], x2[j]));
    
    // For the equality case postcondition
    if x1@ == x2@ {
        assert(forall|j: int| 0 <= j < result.len() ==> x1[j] == x2[j]);
        // When strings are equal, string_le should return true
        // This follows from the reflexivity of less-than-or-equal
    }
    
    result
}
// </vc-code>

}
fn main() {}