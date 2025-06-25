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

fn toMultiset(s: String) -> (mset: multiset<char>)
    ensures
        multiset(s) == mset
{
    return 0;
}

}