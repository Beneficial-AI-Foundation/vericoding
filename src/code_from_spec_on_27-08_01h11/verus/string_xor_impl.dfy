use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn xor_char(c1: char, c2: char) -> char {
    if c1 == c2 { '0' } else { '1' }
}

proof fn xor_char_is_binary(c1: char, c2: char)
    requires
        c1 == '0' || c1 == '1',
        c2 == '0' || c2 == '1',
    ensures
        xor_char(c1, c2) == '0' || xor_char(c1, c2) == '1',
{
}

proof fn xor_char_correctness(c1: char, c2: char)
    requires
        c1 == '0' || c1 == '1',
        c2 == '0' || c2 == '1',
    ensures
        xor_char(c1, c2) == (if c1 == c2 { '0' } else { '1' }),
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
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> (result[j] == '0' || result[j] == '1'),
            forall|j: int| 0 <= j && j < i ==> result[j] == (if a[j] == b[j] { '0' } else { '1' }),
        decreases a.len() - i
    {
        let xor_result = if a[i] == b[i] { '0' } else { '1' };
        result.push(xor_result);
        
        proof {
            assert(a[i as int] == '0' || a[i as int] == '1');
            assert(b[i as int] == '0' || b[i as int] == '1');
            assert(xor_result == '0' || xor_result == '1');
            assert(xor_result == (if a[i as int] == b[i as int] { '0' } else { '1' }));
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}