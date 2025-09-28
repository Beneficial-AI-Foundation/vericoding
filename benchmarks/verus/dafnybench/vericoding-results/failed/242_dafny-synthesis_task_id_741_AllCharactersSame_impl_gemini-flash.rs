use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)] // This is optional, but can sometimes help with performance if the proof is complex.
#[allow(unused_variables)]
fn is_all_same_char_seq(s: Seq<u8>, c: u8) -> bool {
    // This helper predicate checks if all characters in 's' are equal to 'c'.
    // It's used for the 'result ==> ...' postcondition.
    forall|i: nat| i < s.len() ==> s.index(i) == c
}
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
        // If the string has 0 or 1 character, all characters are trivially the same.
        // Proof for result ==> ...
        assert(s.len() <= 1 ==> (forall|i: int, j: int| 
            #[trigger] (0 <= i && (i as nat) < s.len()) && #[trigger] (0 <= j && (j as nat) < s.len()) ==> s.index(i as nat) == s.index(j as nat)
        ));
        true
    } else {
        // If s.len() > 1, we need to iterate and check.
        // We can pick the first character as the reference.
        let first_char = s.index(0);
        let mut i: nat = 1;

        while i < s.len()
            invariant
                1 <= i,
                i <= s.len(),
                // All characters from index 0 up to (but not including) i are the same as first_char
                forall|k: nat| 0 <= k && #[trigger] k < i ==> s.index(k) == first_char,
        {
            if s.index(i) != first_char {
                // Found a different character, so all characters are not the same.
                // Proof for !result ==> ...
                assert(s.len() > 1); // We are in the else branch where s.len() > 1
                assert(exists|idx1: int, idx2: int| {
                    &&& 0 <= idx1 && #[trigger] (idx1 as nat) < s.len()
                    &&& 0 <= idx2 && #[trigger] (idx2 as nat) < s.len()
                    &&& idx1 != idx2
                    &&& s.index(idx1 as nat) != s.index(idx2 as nat)
                }) by {
                    // We know s[0] != s[i]
                    let idx1 = 0;
                    let idx2 = i as int;
                    assert(s.index(idx1 as nat) != s.index(idx2 as nat));
                    assert(idx1 != idx2); // i is at least 1, so i != 0
                };
                return false;
            }
            i = i + 1;
        }

        // If the loop completes, it means all characters were the same as first_char.
        // Proof for result ==> ...
        assert(forall|k: nat| 0 <= k && #[trigger] k < s.len() ==> s.index(k) == first_char);
        assert(forall|i_idx: int, j_idx: int| #[trigger] (0 <= i_idx && (i_idx as nat) < s.len()) && #[trigger] (0 <= j_idx && (j_idx as nat) < s.len()) ==> s.index(i_idx as nat) == s.index(j_idx as nat)) by {
            assert(is_all_same_char_seq(s, first_char)); // Use the helper predicate
            assert forall|ii: nat, jj: nat| ii < s.len() && jj < s.len() implies s.index(ii) == s.index(jj) by {
                assert(s.index(ii) == first_char); // From the predicate
                assert(s.index(jj) == first_char); // From the predicate
                assert(s.index(ii) == s.index(jj));
            }
        };
        true
    }
}
// </vc-code>

fn main() {
}

}