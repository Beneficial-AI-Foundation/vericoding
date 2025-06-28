// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Filter(a: Seq<char>, b: set<char>) -> (c: set<char>)
    ensures
        forall x :: x in a && x in b <==> x in c
{
    return 0;
}

}