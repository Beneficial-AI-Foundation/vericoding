use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to establish the relationship between bytes and string characters
proof fn bytes_to_char_lemma(s: &str, i: usize)
    requires
        0 <= i < s@.len(),
    ensures
        s.as_bytes()[i] == b'.' ==> s@[i as int] == '.',
{
    // This lemma establishes that when a byte at position i is b'.', 
    // the corresponding character in the string view is '.'
}
// </vc-helpers>

// <vc-spec>
fn is_decimal_with_two_precision(s: &str) -> (result: bool)
    ensures
        result ==> exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
        !result ==> !exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let bytes = s.as_bytes();
    
    while i < bytes.len()
        invariant
            0 <= i <= bytes.len(),
            bytes.len() == s@.len(),
            bytes@.len() == s@.len(),
            forall|j: int| 0 <= j < i as int ==> bytes@[j] != b'.' || s@.len() - j - 1 != 2,
            forall|j: int| 0 <= j < bytes@.len() ==> (bytes@[j] == b'.' <==> s@[j] == '.'),
    {
        if bytes[i] == b'.' {
            if bytes.len() - i - 1 == 2 {
                assert(bytes@[i as int] == b'.');
                assert(s@[i as int] == '.');
                assert(0 <= i as int < s@.len());
                assert(s@.len() - (i as int) - 1 == 2);
                return true;
            }
        }
        i = i + 1;
    }
    
    assert(i == bytes.len());
    assert(forall|j: int| 0 <= j < s@.len() ==> bytes@[j] != b'.' || s@.len() - j - 1 != 2);
    assert(forall|j: int| 0 <= j < s@.len() ==> (bytes@[j] == b'.' ==> s@[j] == '.'));
    assert(forall|j: int| 0 <= j < s@.len() ==> s@[j] != '.' || s@.len() - j - 1 != 2);
    false
}
// </vc-code>

fn main() {
}

}