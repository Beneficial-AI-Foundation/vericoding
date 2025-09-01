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

    // Loop through the input slices, XORing characters
    // and pushing them to the result vector.
    // The invariant ensures that intermediate states maintain
    // the property needed for the postcondition.
    proof {
        assert forall|i: int| 0 <= i < common_len as int implies is_binary_digit(#[trigger] a[i]);
        assert forall|i: int| 0 <= i < common_len as int implies is_binary_digit(#[trigger] b[i]);
    }
    let mut i = 0;
    while i < common_len
        invariant
            0 <= i <= common_len,
            result.len() == i,
            result.len() <= common_len,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == xor_char(a[j], b[j]),
            forall|k: int| 0 <= k < a.len() as int ==> is_binary_digit(#[trigger] a[k]),
            forall|l: int| 0 <= l < b.len() as int ==> is_binary_digit(#[trigger] b[l]),
    {
        let char_a = a[i];
        let char_b = b[i];

        // Proof obligations for recommends clause of xor_char
        proof {
            assert(is_binary_digit(char_a));
            assert(is_binary_digit(char_b));
        }

        let xored_char = xor_char(char_a, char_b);
        result.push(xored_char);
        i += 1;
    }

    result
}
// </vc-code>

fn main() {}
}