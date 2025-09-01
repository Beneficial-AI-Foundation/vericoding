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
// Updated helpers section: no additional helpers required for this proof.
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
        invariant i <= n && result.len() == i && forall|j: int| 0 <= j && j < (i as int) ==> result@[j] == xor_char(a@[j], b@[j]);
        decreases n - i;
    {
        let ch: char = if a[i] == b[i] { '0' } else { '1' };
        result.push(ch);
        proof {
            // After push, length increased by 1 and the new element equals ch
            assert(result@.len() == (i as int) + 1);
            assert(result@[i as int] == ch);
            // Use the loop invariant for previous indices
            assert(forall|j: int| 0 <= j && j < (i as int) ==> result@[j] == xor_char(a@[j], b@[j]));
            // ch corresponds to xor_char at this index
            assert(ch == xor_char(a@[i as int], b@[i as int]));
            // Combine to reestablish the invariant for i+1
            assert(forall|j: int| 0 <= j && j < (i as int) + 1 ==>
                result@[j] == xor_char(a@[j], b@[j]));
        }
        i += 1;
    }
    proof {
        // Use invariants and loop exit to conclude final properties
        assert(result.len() == i);
        assert(i >= n);
        assert(i <= n);
        assert(i == n);
        assert(result.len() == n);
        assert(forall|j: int| 0 <= j && j < result.len() as int ==>
            result@[j] == xor_char(a@[j], b@[j]));
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}