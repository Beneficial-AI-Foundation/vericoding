use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers as the issue was in the implementation syntax
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] + b[i] == c[i],
// </vc-spec>
// </vc-spec>

// <vc-code>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a@[i] + b@[i] == c@[i],
{
    let mut result: Vec<i32> = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j] + b@[j],
    {
        result.push(a@[i] + b@[i]);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}

}