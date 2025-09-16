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
/* helper modified by LLM (iteration 3): executable counterpart of xor_char for use in code and invariants */
fn xor_char_exec(a: char, b: char) -> (r: char)
    ensures
        r == xor_char(a, b),
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
    /* code modified by LLM (iteration 3): implement loop building result, use helper to match spec, fix int/usize issues by using i as measure */
    let n: usize = a.len();
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a.len(),
            a.len() == b.len(),
            i <= n,
            res.len() == i,
            forall|j: int|
                0 <= j < i as int ==> #[trigger] res@[j] == xor_char(a[j], b[j]),
        decreases n as int - i as int
    {
        let x: char = xor_char_exec(a[i], b[i]);
        res.push(x);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}