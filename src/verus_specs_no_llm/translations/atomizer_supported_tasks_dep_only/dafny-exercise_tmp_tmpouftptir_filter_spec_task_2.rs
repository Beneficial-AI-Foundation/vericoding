// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Filter(a: Seq<char>, b: set<char>) -> (c: set<char>)
    ensures forall|x: int| x in a and x in b <==> x in c
{
}

}