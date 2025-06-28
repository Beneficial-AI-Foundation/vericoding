// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
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