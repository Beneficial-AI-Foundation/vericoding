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
// (No helpers needed)
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
    let n: nat = a@.len();

    let mut result: Vec<char> = Vec::new();

    let mut i: nat = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> #[trigger] result[j] == xor_char(a[j], b[j]),
    {
        // obtain chars at index i
        let ai: char = a[i];
        let bi: char = b[i];

        // we can rely on the preconditions to know these are binary digits
        proof {
            assert(0 <= i as int && i as int < a@.len() as int);
            assert(is_binary_digit(a[i]));
            assert(is_binary_digit(b[i]));
            assert(is_binary_digit(ai));
            assert(is_binary_digit(bi));
        }

        // compute xor concretely in executable code
        result.push(if ai == bi { '0' } else { '1' });

        // show the new element satisfies the spec-level xor_char relation
        proof {
            assert(result.len() == i + 1);
            if ai == bi {
                assert(result[i] == '0');
                assert(xor_char(ai, bi) == '0');
            } else {
                assert(result[i] == '1');
                assert(xor_char(ai, bi) == '1');
            }
            assert(result[i] == xor_char(ai, bi));
        }

        i = i + 1;
    }

    result
    // impl-end
}
// </vc-code>

fn main() {}
}