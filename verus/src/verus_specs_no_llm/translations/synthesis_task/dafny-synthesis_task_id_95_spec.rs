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

fn SmallestListLength(s: Seq<Seq<int>>) -> (v: int)
    requires
        s.len() > 0
    ensures
        forall i :: 0 <= i < s.len() ==> v <= s.spec_index(i).len(),
        exists i :: 0 <= i < s.len() && v == s.spec_index(i).len()
{
    return 0;
}

}