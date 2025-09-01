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
    let n: int = a.len() as int;

    fn rec(a: &[char], b: &[char], n: int) -> (res: Vec<char>)
        requires a.len() as int == b.len() as int,
        requires 0 <= n && n <= a.len() as int,
        ensures res.len() as int == n,
        ensures forall|i: int| 0 <= i && i < n ==>
            res[i as usize] == (if a[i as usize] == b[i as usize] { '0' } else { '1' }),
        decreases n
    {
        if n == 0 {
            Vec::new()
        } else {
            let mut res = rec(a, b, n - 1);
            let i: int = n - 1;
            let ai: char = a[i as usize];
            let bi: char = b[i as usize];
            let ri: char = if ai == bi { '0' } else { '1' };
            res.push(ri);
            res
        }
    }

    rec(a, b, n)
    // impl-end
}
// </vc-code>

fn main() {}
}