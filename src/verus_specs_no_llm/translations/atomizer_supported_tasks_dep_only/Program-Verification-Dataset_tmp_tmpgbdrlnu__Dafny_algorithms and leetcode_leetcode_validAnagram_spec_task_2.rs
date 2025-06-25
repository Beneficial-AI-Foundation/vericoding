// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn msetEqual(s: multiset<char>, t: multiset<char>) -> (equal: bool)
    ensures s == t <==> equal
{
}

}