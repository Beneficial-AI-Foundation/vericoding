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
// No helpers needed for this implementation.
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
    // impl-start
    let n = a.len();
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n;
        invariant result.len() == i;
        invariant forall |j: int| 0 <= j && j < i as int ==>
            #[trigger] result@[j as usize] == xor_char(a@[j as usize], b@[j as usize]);
        decreases n - i
    {
        result.push(xor_char(a[i], b[i]));
        i += 1;
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}