use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    let n: int = a.len();
    let mut res: Vec<char> = Vec::new();

    let mut i: int = 0;
    while i < n {
        invariant(0 <= i && i <= n);
        invariant(res.len() == i);
        invariant(forall|j: int| 0 <= j && j < i ==> (res[j] == '0' || res[j] == '1'));
        invariant(forall|j: int| 0 <= j && j < i ==> res[j] == (if a[j] == b[j] { '0' } else { '1' }));
        decreases(n - i);

        let c: char = if a[i] == b[i] { '0' } else { '1' };
        res.push(c);

        i += 1;
    }

    res
}
// </vc-code>

fn main() {}
}