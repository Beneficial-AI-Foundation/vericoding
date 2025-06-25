// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn IsSublist(sub: Seq<int>, main: Seq<int>) -> (result: bool)
    ensures true <== (exists|i: int| 0 <= i <= main.len() - sub.len() and sub == main[i..i + sub.len()])
{
}

}