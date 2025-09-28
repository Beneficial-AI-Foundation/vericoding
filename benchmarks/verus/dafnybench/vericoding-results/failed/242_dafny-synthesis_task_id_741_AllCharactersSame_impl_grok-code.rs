use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed
// </vc-helpers>

// <vc-spec>
fn all_characters_same(s: Seq<u8>) -> (result: bool)
    ensures
        result ==> (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]),
        !result ==> (s.len() > 1) && (exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s[i] != s[j])
// </vc-spec>
// <vc-code>
{
    let n = s.len();
    if n <= 1 {
        return true;
    }
    #[invariant(1 <= i <= (n as usize), forall|k: int| 1 <= k < i ==> s@[k] == s@[0])]
    for i in 1..(n as usize) {
        if s@[i] != s@[0] {
            return false;
        }
    }
    true
}
// </vc-code>

fn main() {
}

}