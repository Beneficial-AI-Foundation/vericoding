use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// (no helpers needed)
 
// </vc-helpers>
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
    let n: int = a.len() as int;
    let mut result: Vec<char> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant { 0 <= i && i <= n }
        invariant { result.len() as int == i }
        invariant { forall|j: int| 0 <= j && j < i ==>
            result[j as usize] == (if a[j as usize] == b[j as usize] { '0' } else { '1' }) }
        invariant { b.len() as int == n }
    {
        let ai: char = a[i as usize];
        let bi: char = b[i as usize];
        let ri: char = if ai == bi { '0' } else { '1' };
        result.push(ri);
        i = i + 1;
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}