// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn SplitStringIntoChars(s: String) -> (v: Seq<char>)
    ensures
        v.len() == s.len(),
        forall i :: 0 <= i < s.len() ==> v.spec_index(i) == s.spec_index(i)
{
    return Seq::empty();
}

}