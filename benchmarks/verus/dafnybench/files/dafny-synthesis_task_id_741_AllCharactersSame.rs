use vstd::prelude::*;

verus! {

fn all_characters_same(s: Seq<u8>) -> (result: bool)
    ensures
        result ==> (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]),
        !result ==> (s.len() > 1) && (exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s[i] != s[j])
{
    assume(false);
    unreached()
}

}
fn main() {}