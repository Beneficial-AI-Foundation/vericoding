// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IsSublist(sub: Seq<int>, main: Seq<int>) -> result: bool
    ensures
        true <== (exists |i: int| 0 <= i <= main.len() - sub.len() && sub == main.index(i..i + sub.len()))
;

proof fn lemma_IsSublist(sub: Seq<int>, main: Seq<int>) -> (result: bool)
    ensures
        true <== (exists |i: int| 0 <= i <= main.len() - sub.len() && sub == main.index(i..i + sub.len()))
{
    false
}

}