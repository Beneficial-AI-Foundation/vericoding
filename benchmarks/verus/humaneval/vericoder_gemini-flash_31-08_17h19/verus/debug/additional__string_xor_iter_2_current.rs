use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    // impl-start
    let mut result: Vec<char> = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            result.capacity() == a.len(),
            forall|j: int| 0 <= j && (j as usize) < i ==> (result[j as usize] == '0' || result[j as usize] == '1'),
            forall|j: int| 0 <= j && (j as usize) < i ==> result[j as usize] == (if a[j as usize] == b[j as usize] { '0' } else { '1' }),
    {
        let res_char: char;
        if a[i] == b[i] {
            res_char = '0';
        } else {
            res_char = '1';
        }
        result.push(res_char);
        i = i + 1;
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}