// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn toMultiset(s: String) -> (mset: multiset<char>)
    ensures multiset(s) == mset
{
}

}