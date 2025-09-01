use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_element(a: &[i32], pos: usize) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        0 <= pos < a.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < pos ==> result[i] == a[i],
        forall|i: int| pos <= i < result.len() ==> result[i] == a[i + 1],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            0 <= pos < a.len(),
            result.len() == if i <= pos { i } else { i - 1 },
            forall|j: int| 0 <= j < pos && j < i ==> result[j] == a[j],
            forall|j: int| pos < j < i ==> result[j - 1] == a[j],
    {
        if i != pos {
            result.push(a[i]);
        }
        i += 1;
    }
    
    assert(result.len() == a.len() - 1);
    assert(forall|j: int| 0 <= j < pos ==> result[j] == a[j]);
    assert(forall|j: int| pos <= j < result.len() ==> result[j] == a[j + 1]);
    
    result
}
// </vc-code>

fn main() {}
}