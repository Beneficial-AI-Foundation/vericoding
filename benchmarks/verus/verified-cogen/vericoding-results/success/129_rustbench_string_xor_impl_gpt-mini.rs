// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): char_xor returns '0' when equal else '1' */
fn char_xor(a: char, b: char) -> (result: char)
    requires
        a == '0' || a == '1',
        b == '0' || b == '1',
    ensures
        result == (if a == b { '0' } else { '1' }),
{
    if a == b { '0' } else { '1' }
}

/* helper modified by LLM (iteration 5): predicate for bit chars */
spec fn is_bit(c: char) -> bool { c == '0' || c == '1' }
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
    /* code modified by LLM (iteration 5): use usize index for runtime and int casts in invariants, use char_xor */
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int && i as int <= a.len() as int,
            res.len() == i,
            forall|j: int| 0 <= j && j < res.len() as int ==> res@[j] == (if a@[j] == b@[j] { '0' } else { '1' }),
        decreases
            a.len() as int - i as int
    {
        let ai = a[i];
        let bi = b[i];
        let r = char_xor(ai, bi);
        res.push(r);
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}