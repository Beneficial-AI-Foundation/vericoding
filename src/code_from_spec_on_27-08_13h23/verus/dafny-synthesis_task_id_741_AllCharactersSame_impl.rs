use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn all_characters_same(s: Seq<u8>) -> (result: bool)
    ensures
        result ==> (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]),
        !result ==> (s.len() > 1) && (exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s[i] != s[j])
// </vc-spec>
// </vc-spec>

// <vc-code>
fn all_characters_same(s: Seq<u8>) -> (result: bool)
    ensures
        result ==> (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]),
        !result ==> (s.len() > 1) && (exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s[i] != s[j])
{
    if s.len() <= 1 {
        return true;
    }
    
    let first = s[0];
    let mut i: usize = 1;
    
    while i < s.len()
        invariant
            0 < i <= s.len(),
            forall|k: int| 0 <= k < i ==> s[k] == first
    {
        if s[i] != first {
            return false;
        }
        i = i + 1;
    }
    
    true
}
// </vc-code>

fn main() {
}

}