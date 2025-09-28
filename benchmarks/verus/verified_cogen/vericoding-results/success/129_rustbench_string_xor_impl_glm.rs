// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn string_xor(a: &[char], b: &[char]) -> (result: Vec<char>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i && i < a.len() ==> a[i] == '0' || a[i] == '1',
        forall|i: int| 0 <= i && i < b.len() ==> b[i] == '0' || b[i] == '1',
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> (result[i] == '0' || result[i] == '1'),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == (if a[i] == b[i] { '0' } else { '1' })
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (if a[j] == b[j] { '0' } else { '1' }),
            forall|j: int| 0 <= j < i ==> (result[j] == '0' || result[j] == '1')
    {
        let c = if a[i] == b[i] { '0' } else { '1' };
        result.push(c);
    }
    result
}
// </vc-code>

}
fn main() {}