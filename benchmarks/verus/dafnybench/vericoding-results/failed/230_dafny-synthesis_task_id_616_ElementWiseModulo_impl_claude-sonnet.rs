use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn element_wise_modulo(a: &[i32], b: &[i32]) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            a.len() == b.len(),
            forall|j: int| #![trigger result@[j]] 0 <= j < i ==> result@[j] == a@[j] % b@[j],
        decreases a.len() - i,
    {
        assert(i < a.len());
        assert(a.len() == b.len());
        assert(i < b.len());
        assert(b@[i as int] != 0);
        result.push(a[i] % b[i]);
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}