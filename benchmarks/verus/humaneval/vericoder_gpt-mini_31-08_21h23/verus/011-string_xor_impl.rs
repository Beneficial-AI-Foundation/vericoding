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
// No helper definitions needed for this example.
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
    let n: int = a@.len() as int;
    let mut result: Vec<char> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant result.len() as int == i;
        invariant forall |j: int| 0 <= j && j < i ==>
            #[trigger] result@[j as usize] == xor_char(a@[j as usize], b@[j as usize]);
        decreases n - i
    {
        result.push(xor_char(a[i as usize], b[i as usize]));
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}