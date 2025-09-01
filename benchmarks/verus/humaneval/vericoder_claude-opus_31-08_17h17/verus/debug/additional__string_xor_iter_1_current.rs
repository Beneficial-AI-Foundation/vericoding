use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn string_xor(a: &[char], b: &[char]) -> (result: Vec<char>)
    // pre-conditions-start
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i && i < a.len() ==> a[i] == '0' || a[i] == '1',
        forall|i: int| 0 <= i && i < b.len() ==> b[i] == '0' || b[i] == '1',
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> (result[i] == '0' || result[i] == '1'),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == (if a[i] == b[i] { '0' } else { '1' })
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> (result[j] == '0' || result[j] == '1'),
            forall|j: int| 0 <= j && j < i ==> result[j] == (if a[j] == b[j] { '0' } else { '1' }),
    {
        let xor_result = if a[i] == b[i] { '0' } else { '1' };
        result.push(xor_result);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}