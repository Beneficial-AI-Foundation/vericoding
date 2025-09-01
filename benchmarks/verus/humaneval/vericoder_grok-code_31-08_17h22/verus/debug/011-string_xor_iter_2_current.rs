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
// <vc-helpers>
// </vc-helpers>
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
    let mut result: Vec<char> = Vec::new();
    let len: usize = a.len();
    let mut i: usize = 0;
    while i < len
    // pure-end
        invariant
            i <= len,
            result@.len() as int == i as int,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j] == xor_char(a@[j], b@[j]),
        decreases
            len as int - i as int,
    {
        let xor_val: char;
        if a[i] == b[i] {
            xor_val = '0';
        } else {
            xor_val = '1';
        }
        result.push(xor_val);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}