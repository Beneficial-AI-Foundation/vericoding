// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_bit(c: char) -> bool { c == '0' || c == '1' }

spec fn xor_char(a: char, b: char) -> char { if a == b { '0' } else { '1' } }

proof fn xor_char_is_bit(a: char, b: char)
    requires
        is_bit(a),
        is_bit(b),
    ensures
        is_bit(xor_char(a, b))
{ }
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
    let n = a.len();
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a.len(),
            n == b.len(),
            i <= n,
            res.len() == i,
            forall|k: int|
                0 <= k && k < i as int ==> (res@[k] == '0' || res@[k] == '1'),
            forall|k: int|
                0 <= k && k < i as int ==> res@[k] == (if a[k] == b[k] { '0' } else { '1' }),
        decreases n as int - i as int
    {
        let ai = a[i];
        let bi = b[i];
        let c = if ai == bi { '0' } else { '1' };
        let ghost prev = res@;
        res.push(c);
        i += 1;
        proof {
            assert(res@ == prev.push(c));
        }
    }
    assert(i == n);
    res
}
// </vc-code>

}
fn main() {}