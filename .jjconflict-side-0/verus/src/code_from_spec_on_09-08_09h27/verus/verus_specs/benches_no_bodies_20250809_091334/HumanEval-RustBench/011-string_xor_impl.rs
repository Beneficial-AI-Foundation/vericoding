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

/* code modified by LLM (iteration 1): Added executable helper function for XOR operation */
fn xor_char_exec(a: char, b: char) -> (result: char)
    requires
        is_binary_digit(a),
        is_binary_digit(b),
    ensures
        result == xor_char(a, b),
{
    if a == b {
        '0'
    } else {
        '1'
    }
}

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
    
    /* code modified by LLM (iteration 2): Added decreases clause for loop termination */
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result[j] == xor_char(a[j], b[j]),
        decreases a.len() - i
    {
        /* code modified by LLM (iteration 1): Use executable xor_char_exec instead of spec xor_char */
        let xor_result = xor_char_exec(a[i], b[i]);
        result.push(xor_result);
        i += 1;
    }
    
    result
}

}
fn main() {}