// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no changes required in this turning */
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
/* code modified by LLM (iteration 4): Add `decreases a.len() - i` to resolve loop decreases clause error. */
{
    let mut result_vec: Vec<char> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j && j < i ==> (result_vec@[j] == '0' || result_vec@[j] == '1'),
            forall|j: int| 0 <= j && j < i ==> result_vec@[j] == (if a[j] == b[j] { '0' } else { '1' })
        decreases a.len() - i
    {
        let char_a = a[i];
        let char_b = b[i];
        let xor_char = if char_a == char_b { '0' } else { '1' };
        result_vec.push(xor_char);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}