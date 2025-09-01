use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn xor_char_property(a: char, b: char)
    requires
        a == '0' || a == '1',
        b == '0' || b == '1',
    ensures
        (if a == b { '0' } else { '1' }) == '0' || (if a == b { '0' } else { '1' }) == '1'
{
}

proof fn char_eq_proof(a: char, b: char, c: char, d: char)
    requires
        a == '0' || a == '1',
        b == '0' || b == '1',
        c == '0' || c == '1',
        d == '0' || d == '1',
    ensures
        (a == c && b == d) ==> (if a == b { '0' } else { '1' }) == (if c == d { '0' } else { '1' })
{
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn string_xor(a: &[char], b: &[char]) -> (result: Vec<char>)
    // pre-conditions-start
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i && i < a.len() ==> a[i] == '0' || a[i] == '1',
        forall|i: int| 0 <= i && i < b.len() ==> b[i] == '0' || b[i] == '1',
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> (result[i] == '0' || result[i] == '1'),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == (if a[i] == b[i] { '0' } else { '1' })
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == '0' || result[j] == '1',
            forall|j: int| 0 <= j && j < i ==> result[j] == (if a[j] == b[j] { '0' } else { '1' })
        decreases a.len() - i
    {
        let a_char = a[i];
        let b_char = b[i];
        assert(a_char == '0' || a_char == '1') by {
            assert(forall|k: int| 0 <= k && k < a.len() ==> a[k] == '0' || a[k] == '1');
        };
        assert(b_char == '0' || b_char == '1') by {
            assert(forall|k: int| 0 <= k && k < b.len() ==> b[k] == '0' || b[k] == '1');
        };
        
        let xor_result = if a_char == b_char { '0' } else { '1' };
        proof {
            xor_char_property(a_char, b_char);
        }
        
        result.push(xor_result);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}