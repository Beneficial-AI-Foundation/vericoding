use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn all_characters_same(s: Seq<u8>) -> (result: bool)
    ensures
        result ==> (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]),
        !result ==> (s.len() > 1) && (exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s[i] != s[j])
// </vc-spec>
// <vc-code>
{
    if s.len() == 0 {
        true
    } else {
        let x = s[0];
        let all = forall|i: int| 0 <= i < s.len() ==> s[i] == x;
        if all {
            true
        } else {
            proof {
                assert(s.len() > 0);

                // From !all, obtain an index with a differing value
                assert(exists|i: int| 0 <= i < s.len() && s[i] != x);
                let i_w = choose|i: int| 0 <= i < s.len() && s[i] != x;
                assert(0 <= i_w < s.len());
                assert(s[i_w] != x);

                // i_w must differ from 0, hence length >= 2
                assert(i_w != 0);
                assert(i_w >= 1);
                assert(i_w + 1 <= s.len());
                assert(s.len() >= 2);

                // Provide witnesses (i_w, 0) for the postcondition existential
                assert(exists|i: int, j: int|
                    0 <= i < s.len() && 0 <= j < s.len() && i != j && s[i] != s[j]
                ) by {
                    exists(i_w, 0);
                }
            }
            false
        }
    }
}
// </vc-code>

fn main() {
}

}