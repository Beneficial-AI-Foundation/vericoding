// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add precondition to prevent overflow */
fn can_invert_safely(value: i32) -> (result: bool)
    ensures result == (value != i32::MIN)
{
    value != i32::MIN
}

fn safe_invert(value: i32) -> (result: i32)
    requires value != i32::MIN
    ensures result == -(value + 1)
{
    -(value + 1)
}
// </vc-helpers>

// <vc-spec>
fn invert(x: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] == -(x[i] + 1),
        forall|i: int| 0 <= i < x.len() && x[i] == 0 ==> result[i] == -1,
        forall|i: int| 0 <= i < x.len() && x[i] == -1 ==> result[i] == 0,
        forall|i: int| 0 <= i < x.len() && x[i] != -1 ==> (x[i] > 0 <==> result[i] < 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix type mismatch by converting index to int */
    let mut result = Vec::new();
    let mut i = 0;
    
    // Check all values can be safely inverted
    while i < x.len()
        invariant i <= x.len()
        decreases x.len() - i
    {
        assert(x[i as int] != i32::MIN);
        i += 1;
    }
    
    i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == -(x[j] + 1)
        decreases x.len() - i
    {
        let current_val = x[i as int];
        let inverted_value = -(current_val + 1);
        result.push(inverted_value);
        i += 1;
    }
    
    proof {
        assert(result.len() == x.len());
        assert(forall|j: int| 0 <= j < x.len() ==> result[j] == -(x[j] + 1));
        
        // The remaining postconditions follow from the arithmetic properties
        assert(forall|j: int| 0 <= j < x.len() && x[j] == 0 ==> -(x[j] + 1) == -1);
        assert(forall|j: int| 0 <= j < x.len() && x[j] == -1 ==> -(x[j] + 1) == 0);
        
        // For the sign relationship: if x[j] > 0, then -(x[j] + 1) < 0
        // if x[j] < 0 and x[j] != -1, then x[j] <= -2, so -(x[j] + 1) >= 1 > 0
        assert(forall|j: int| 0 <= j < x.len() && x[j] != -1 && x[j] > 0 ==> -(x[j] + 1) < 0);
        assert(forall|j: int| 0 <= j < x.len() && x[j] != -1 && x[j] <= 0 ==> -(x[j] + 1) >= 1);
    }
    
    result
}
// </vc-code>

}
fn main() {}