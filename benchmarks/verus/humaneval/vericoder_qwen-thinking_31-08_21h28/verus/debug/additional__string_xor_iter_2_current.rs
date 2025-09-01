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
    let n = a.len();
    let mut result = Vec::new();
    let mut i = 0;
    while i < n {
        invariant i <= n;
        invariant result.len() == i;
        invariant forall |j: int| 0 <= j < i ==> result[j] == (if a[j] == b[j] { '0' } else { '1' });

        if a[i] == b[i] {
            result.push('0');
        } else {
            result.push('1');
        }
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}