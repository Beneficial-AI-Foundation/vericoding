use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn concat(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    ensures 
        c.len() == b.len() + a.len(),
        forall|k: int| 0 <= k < a.len() ==> c[k] == a[k],
        forall|k: int| 0 <= k < b.len() ==> c[k + a.len()] == b[k],
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == a[k],
    {
        result.push(a[i]);
    }
    
    for i in 0..b.len()
        invariant
            result.len() == a.len() + i,
            forall|k: int| 0 <= k < a.len() ==> result[k] == a[k],
            forall|k: int| 0 <= k < i ==> result[k + a.len()] == b[k],
    {
        result.push(b[i]);
    }
    
    result
}
// </vc-code>

fn main() {
}

}