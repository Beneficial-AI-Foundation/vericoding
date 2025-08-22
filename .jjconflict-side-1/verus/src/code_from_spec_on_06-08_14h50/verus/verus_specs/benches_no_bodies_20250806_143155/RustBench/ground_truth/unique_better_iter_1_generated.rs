use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn unique_better(a: &[i32]) -> (result: Vec<i32>)
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
{
    let mut result = Vec::new();
    
    for i in 0..a.len()
        invariant
            forall|x: int, y: int|
                #![trigger result[x], result[y]]
                0 <= x && x < y && y < result.len() ==> result[x] < result[y],
    {
        if result.len() == 0 || a[i] != result[result.len() - 1] {
            result.push(a[i]);
        }
    }
    
    result
}

fn main() {}
}