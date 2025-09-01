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
spec fn xor_char_spec(a: char, b: char) -> (result: char)
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

proof fn xor_char_proof(a: char, b: char)
    requires
        is_binary_digit(a),
        is_binary_digit(b),
    ensures
        xor_char(a, b) == xor_char_spec(a, b),
{
}

spec fn result_invariant(a: Seq<char>, b: Seq<char>, result: Seq<char>) -> bool {
    result.len() == a.len() &&
    forall|i: int| 0 <= i < result.len() ==> result[i] == xor_char(a[i], b[i])
}

proof fn loop_invariant(vec: &[char], i: int, result: Vec<char>, a: Seq<char>, b: Seq<char>)
    requires
        0 <= i <= (a.len() as int),
        a.len() == b.len(),
        result.len() == (i as nat),
        forall|j: int| 0 <= j < i ==> result@[j] == xor_char(a[j], b[j]),
        forall|k: int| 0 <= k < a.len() ==> is_binary_digit(a[k as int]),
        forall|k: int| 0 <= k < b.len() ==> is_binary_digit(b[k as int]),
{
}
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
    let len = a.len();
    let mut result: Vec<char> = Vec::new();
    
    proof {
        assert(result@.len() == 0);
    }
    
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == xor_char(a@[j], b@[j]),
        decreases len - i,
    {
        let ac = a[i];
        let bc = b[i];
        
        proof {
            assert(is_binary_digit(ac));
            assert(is_binary_digit(bc));
            xor_char_proof(ac, bc);
        }
        
        let xc = if ac == bc { '0' } else { '1' };
        
        proof {
            assert(xc == xor_char(ac, bc));
        }
        
        result.push(xc);
        
        proof {
            let old_result = result@.drop_last();
            assert forall|j: int| 0 <= j < i implies result@[j] == xor_char(a@[j], b@[j]) by {
                assert(old_result[j] == result@[j]);
            };
            assert(result@[i] == xor_char(ac, bc));
        }
        
        i += 1;
    }
    
    proof {
        assert(result@.len() == len);
        assert forall|j: int| 0 <= j < len implies result@[j] == xor_char(a@[j], b@[j]) by {
            if 0 <= j < len {
                assert(result@[j] == xor_char(a@[j], b@[j]));
            }
        };
    }
    
    result
}
// </vc-code>

fn main() {}
}