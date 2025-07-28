use vstd::prelude::*;

verus! {
spec fn is_binary_digit(c: char) -> (ret: bool) {
    c == '0' || c == '1'
}
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
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to fix compilation error */
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            a@.len() == b@.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == xor_char(a[j], b[j]),
        decreases a@.len() - i
    {
        let xor_result = if a[i] == b[i] { '0' } else { '1' };
        result.push(xor_result);
        i = i + 1;
    }
    
    result
}

}
fn main() {}