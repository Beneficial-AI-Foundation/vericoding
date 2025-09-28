use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_to_seq(a: &[i32]) -> (s: Vec<i32>)
    ensures
        s.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> s[i] == a[i],
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j],
        decreases a.len() - i,
    {
        result.push(a[i]);
        i += 1;
    }
    
    assert(i == a.len());
    assert(result.len() == i);
    assert(result.len() == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> result@[j] == a@[j]);
    
    result
}
// </vc-code>

fn main() {
}

}