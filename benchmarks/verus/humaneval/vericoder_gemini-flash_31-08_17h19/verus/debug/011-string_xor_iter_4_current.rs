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
spec fn is_binary_digit(c: char) -> (ret: bool) {
    c == '0' || c == '1'
}

spec fn xor_char_spec(a: char, b: char) -> (result: char)
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
    let common_len = a.len();

    let mut i = 0;
    while i < common_len
        invariant
            0 <= i <= common_len,
            result.len() == i,
            result.len() <= common_len,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == xor_char_spec(a[j], b[j]),
            a.len() == b.len(), // From precondition
            forall|k: int| 0 <= k < a.len() as int ==> is_binary_digit(#[trigger] a[k]), // From precondition
            forall|l: int| 0 <= l < b.len() as int ==> is_binary_digit(#[trigger] b[l]), // From precondition
    {
        let char_a = a[i];
        let char_b = b[i];

        // The recommends clauses for xor_char are guaranteed by the loop invariant,
        // which itself comes from the function's preconditions.
        // Verus can prove these assertions automatically based on the invariant.
        assert(is_binary_digit(char_a));
        assert(is_binary_digit(char_b));

        let xored_char = xor_char_spec(char_a, char_b);
        result.push(xored_char);
        i += 1;
    }

    result
}
// </vc-code>

fn main() {}
}