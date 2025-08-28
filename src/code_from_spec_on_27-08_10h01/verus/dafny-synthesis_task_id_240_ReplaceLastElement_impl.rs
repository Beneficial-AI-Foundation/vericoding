use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn replace_last_element(first: &Vec<i32>, second: &Vec<i32>) -> (result: Vec<i32>)
    requires 
        first.len() > 0,
    ensures 
        result.len() == first.len() - 1 + second.len(),
        forall|i: int| 0 <= i < first.len() - 1 ==> result[i] == first[i],
        forall|i: int| first.len() - 1 <= i < result.len() ==> result[i] == second[i - first.len() + 1],
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    
    // Add all elements from first except the last one
    let mut i = 0;
    while i < first.len() - 1
        invariant
            0 <= i <= first.len() - 1,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == first@[j],
        decreases first.len() - 1 - i
    {
        result.push(first[i]);
        i += 1;
    }
    
    // Add all elements from second
    let mut j = 0;
    while j < second.len()
        invariant
            0 <= j <= second.len(),
            result.len() == first.len() - 1 + j,
            forall|k: int| 0 <= k < first.len() - 1 ==> result@[k] == first@[k],
            forall|k: int| first.len() - 1 <= k < first.len() - 1 + j ==> 0 <= k - (first.len() - 1) < j && result@[k] == second@[k - (first.len() - 1)],
        decreases second.len() - j
    {
        result.push(second[j]);
        j += 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}