use vstd::prelude::*;

verus! {

//ATOM
spec fn is_binary_digit(c: char) -> (ret: bool) {
    c == '0' || c == '1'
}

//ATOM
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

//IMPL string_xor
fn string_xor(a: &[char], b: &[char]) -> (result: Vec<char>)
    requires
        a@.len() == b@.len(),
        forall|i: int| 0 <= i < a@.len() as int ==> is_binary_digit(#[trigger] a[i]),
        forall|i: int| 0 <= i < b@.len() as int ==> is_binary_digit(#[trigger] b[i]),
    ensures
        result.len() == a@.len(),
        forall|i: int|
            0 <= i < result.len() as int ==> #[trigger] result[i] == xor_char(a[i], b[i]),
{
    /* code modified by LLM (iteration 3): Added proper bounds checking and binary digit assertions */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            a@.len() == b@.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result[j] == xor_char(a[j], b[j]),
            forall|j: int| 0 <= j < a@.len() as int ==> is_binary_digit(#[trigger] a[j]),
            forall|j: int| 0 <= j < b@.len() as int ==> is_binary_digit(#[trigger] b[j]),
        decreases a.len() - i
    {
        /* code modified by LLM (iteration 3): Added assertions to prove recommendations are met */
        assert(i < a.len());
        assert(i < b.len());
        assert(is_binary_digit(a[i]));
        assert(is_binary_digit(b[i]));
        
        let xor_result = if a[i] == b[i] {
            '0'
        } else {
            '1'
        };
        result.push(xor_result);
        i += 1;
    }
    
    result
}

}

fn main() {}