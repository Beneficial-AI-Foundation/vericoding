// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn InsertBeforeEach(s: Seq<String>, x: String) -> (v: Seq<String>)
    ensures v.len() == 2 * s.len(),
            forall|i: int| 0 <= i < s.len() ==> v[2*i] == x and v[2*i + 1] == s[i]
{
}

}