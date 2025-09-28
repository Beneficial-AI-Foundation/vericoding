use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
fn all_characters_same(s: Seq<u8>) -> (result: bool)
    ensures
        result ==> (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]),
        !result ==> (s.len() > 1) && (exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s[i] != s[j])
// </vc-spec>
// <vc-code>
{
    if s.len() <= 1 {
        // Empty or single character sequences have all characters the same
        true
    } else {
        // Check if all characters equal the first character
        let first = s[0];
        let mut i: usize = 1;
        while i < s.len()
            invariant
                1 <= i <= s.len(),
                forall|j: int| 0 <= j < i as int ==> s[j] == s[0],
                first == s[0],
        {
            if s[i] != first {
                // Found a character different from the first one
                assert(s[0] == first);
                assert(s[i] != first);
                assert(0 != i as int);
                assert(s[0] != s[i]);
                return false;
            }
            i = i + 1;
        }
        
        // All characters equal the first one
        assert(forall|j: int| 0 <= j < s.len() ==> s[j] == s[0]);
        assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]) by {
            assert forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() implies s[i] == s[j] by {
                assert(s[i] == s[0]);
                assert(s[j] == s[0]);
            }
        }
        true
    }
}
// </vc-code>

fn main() {
}

}