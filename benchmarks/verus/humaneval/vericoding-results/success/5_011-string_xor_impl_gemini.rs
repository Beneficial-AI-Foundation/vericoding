// <vc-preamble>
use vstd::prelude::*;
use vstd::slice::*;

verus! {

spec fn is_binary_digit(c: char) -> (ret: bool) {
    c == '0' || c == '1'
}

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
// </vc-preamble>

// <vc-helpers>
fn compute_xor_char(a: char, b: char) -> (res: char)
    requires
        is_binary_digit(a),
        is_binary_digit(b),
    ensures
        res == xor_char(a, b),
{
    if a == b { '0' } else { '1' }
}
// </vc-helpers>

// <vc-spec>
fn string_xor(a: &[char], b: &[char]) -> (result: Vec<char>)

    requires
        a@.len() == b@.len(),
        forall|i: int| 0 <= i < a@.len() as int ==> is_binary_digit(#[trigger] a[i]),
        forall|i: int| 0 <= i < b@.len() as int ==> is_binary_digit(#[trigger] b[i]),

    ensures
        result.len() == a@.len(),
        forall|i: int|
            0 <= i < result.len() as int ==> #[trigger] result[i] == xor_char(a[i], b[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): strengthened loop invariants */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < a.len() as int ==> is_binary_digit(#[trigger] a[j]),
            forall|j: int| 0 <= j < b.len() as int ==> is_binary_digit(#[trigger] b[j]),
            forall|j: int| 0 <= j < i as int ==> #[trigger] result[j] == xor_char(a[j], b[j]),
        decreases a.len() - i
    {
        let xor_val = compute_xor_char(a[i], b[i]);
        result.push(xor_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}