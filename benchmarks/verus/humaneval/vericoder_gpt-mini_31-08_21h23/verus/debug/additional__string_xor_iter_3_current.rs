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
    let n_usize: usize = a.len();
    let mut res: Vec<char> = Vec::new();

    let mut i: usize = 0;
    while i < n_usize {
        invariant(i <= n_usize);
        invariant(res.len() == i);
        invariant(forall|j: int| 0 <= j && j < (i as int) ==> (res[j as usize] == '0' || res[j as usize] == '1'));
        invariant(forall|j: int| 0 <= j && j < (i as int) ==> res[j as usize] == (if a[j as usize] == b[j as usize] { '0' } else { '1' }));
        decreases((n_usize as int) - (i as int));

        let c: char = if a[i] == b[i] { '0' } else { '1' };
        res.push(c);

        i += 1;
    }

    res
}
// </vc-code>

fn main() {}
}