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
// No additional helpers needed for this implementation
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
    let n = a.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a@.len(),
            n == b@.len(),
            result@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j] == xor_char(a@[j], b@[j]),
            forall|j: int| 0 <= j < a@.len() as int ==> is_binary_digit(#[trigger] a@[j]),
            forall|j: int| 0 <= j < b@.len() as int ==> is_binary_digit(#[trigger] b@[j]),
    {
        let xor_result = if a[i] == b[i] { '0' } else { '1' };
        
        assert(is_binary_digit(a@[i as int]));
        assert(is_binary_digit(b@[i as int]));
        assert(xor_result == xor_char(a@[i as int], b@[i as int]));
        
        result.push(xor_result);
        
        assert(result@.len() == (i + 1) as int);
        assert(result@[i as int] == xor_char(a@[i as int], b@[i as int]));
        
        i = i + 1;
    }
    
    assert(result@.len() == n as int);
    assert(result@.len() == a@.len());
    assert(forall|j: int| 0 <= j < result@.len() as int ==> #[trigger] result@[j] == xor_char(a@[j], b@[j]));
    
    result
}
// </vc-code>

fn main() {}
}