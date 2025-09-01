use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
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
    let n: usize = a.len();
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int,
            res.len() == i,
            forall|k: int| 0 <= k && k < i as int ==>
                res[k as usize] == (if a[k as usize] == b[k as usize] { '0' } else { '1' }),
        decreases n - i
    {
        let ai: char = a[i];
        let bi: char = b[i];
        let ri: char = if ai == bi { '0' } else { '1' };
        res.push(ri);
        i += 1;
    }
    assert(res.len() == n);
    assert(forall|k: int| 0 <= k && k < n as int ==>
        res[k as usize] == (if a[k as usize] == b[k as usize] { '0' } else { '1' })
    );
    res
    // impl-end
}
// </vc-code>

fn main() {}
}