use vstd::prelude::*;

verus! {

// <vc-helpers>
// (No helpers needed)
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
        proof {
            // vacuously true for sequences of length 0 or 1
            assert(forall|i: int, j: int| 0 <= i && i < s.len() && 0 <= j && j < s.len() ==> s[i] == s[j]);
        }
        true
    } else {
        let first: u8 = s[0];
        let mut i: int = 1;
        while i < s.len()
            invariant 1 <= i && i <= s.len();
            invariant forall|k: int| 0 <= k && k < i ==> s[k] == first;
            decreases s.len() - i;
        {
            if s[i] != first {
                proof {
                    // witness a = 0, b = i show there exist distinct indices with unequal values
                    assert(s.len() > 1);
                    assert(0 <= 0 && 0 < s.len());
                    assert(0 <= i && i < s.len());
                    assert(s[0] != s[i]);
                    assert(exists|a: int, b: int| 0 <= a && a < s.len() && 0 <= b && b < s.len() && a != b && s[a] != s[b]);
                }
                return false;
            }
            i = i + 1;
        }
        proof {
            // from the loop invariant at exit (i == s.len()) we have all elements equal to `first`
            assert(i >= s.len());
            assert(i <= s.len());
            assert(i == s.len());
            assert(forall|k: int| 0 <= k && k < i ==> s[k] == first);
            assert(forall|k: int| 0 <= k && k < s.len() ==> s[k] == first);
            // hence all pairs are equal
            assert(forall|i: int, j: int| 0 <= i && i < s.len() && 0 <= j && j < s.len() ==> s[i] == s[j]);
        }
        true
    }
}
// </vc-code>

fn main() {
}

}