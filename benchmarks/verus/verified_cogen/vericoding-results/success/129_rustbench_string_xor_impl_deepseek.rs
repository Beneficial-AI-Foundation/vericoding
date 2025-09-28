// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn xor_char(c1: char, c2: char) -> (result: char)
    requires
        c1 == '0' || c1 == '1',
        c2 == '0' || c2 == '1',
    ensures
        result == (if c1 == c2 { '0' } else { '1' })
{
    if c1 == '0' {
        if c2 == '0' { '0' } else { '1' }
    } else {
        if c2 == '0' { '1' } else { '0' }
    }
}
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
    /* code modified by LLM (iteration 2): Add decreases clause to while loop */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> (result@[j] == '0' || result@[j] == '1'),
            forall|j: int| 0 <= j && j < i ==> result@[j] == (if a@[j] == b@[j] { '0' } else { '1' })
        decreases a.len() - i
    {
        let xor_result = xor_char(a[i], b[i]);
        result.push(xor_result);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}