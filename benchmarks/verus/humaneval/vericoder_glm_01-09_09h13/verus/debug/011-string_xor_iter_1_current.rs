use vstd::prelude::*;
use vstd::slice::*;

verus! {

spec fn is_binary_digit(c: char) -> (ret: bool) {
    c == '0' || c == '1'
}
// pure-end
// pure-end

spec fn xor_char(a: char, b: char) -> (result: char)
    recommends
        is_binary_digit(a),
        is_binary_digit(b),
{
    if a == b {
        '0'
    } else {
        '1'
    }
}
// pure-end

// <vc-helpers>
proof fn xor_char_lemma(a: char, b: char)
    requires
        is_binary_digit(a),
        is_binary_digit(b),
    ensures
        (if a == b { '0' } else { '1' }) == xor_char(a, b)
{
    if a == b {
        assert(xor_char(a, b) == '0');
    } else {
        assert(xor_char(a, b) == '1');
    }
}
// </vc-helpers>

// <vc-spec>
fn string_xor(a: &[char], b: &[char]) -> (result: Vec<char>)
    // pre-conditions-start
    requires
        a@.len() == b@.len(),
        forall|i: int| 0 <= i < a@.len() as int ==> is_binary_digit(#[trigger] a[i]),
        forall|i: int| 0 <= i < b@.len() as int ==> is_binary_digit(#[trigger] b[i]),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == a@.len(),
        forall|i: int|
            0 <= i < result.len() as int ==> #[trigger] result[i] == xor_char(a[i], b[i]),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::with_capacity(a.len());
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == xor_char(a[j], b[j]),
    {
        let x = a[i];
        let y = b[i];
        let c = if x == y { '0' } else { '1' };
        proof {
            xor_char_lemma(x, y);
            assert(c == xor_char(x, y));
        }
        result.push(c);
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}