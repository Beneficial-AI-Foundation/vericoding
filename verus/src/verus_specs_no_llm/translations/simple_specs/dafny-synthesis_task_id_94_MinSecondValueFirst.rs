// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_MinSecondValueFirst(s: Vec<Seq<int>>) -> firstOfMinSecond: int
    requires
        s.len() > 0,
        forall |i: int| 0 <= i < s.len() ==> s.index(i).len() >= 2
    ensures
        exists |i: int| 0 <= i < s.len() && firstOfMinSecond == s.index(i)[0] && 
    (forall |j: int| 0 <= j < s.len() ==> s.index(i)[1] <= s.index(j)[1])
;

proof fn lemma_MinSecondValueFirst(s: Vec<Seq<int>>) -> (firstOfMinSecond: int)
    requires
        s.len() > 0,
        forall |i: int| 0 <= i < s.len() ==> s.index(i).len() >= 2
    ensures
        exists |i: int| 0 <= i < s.len() && firstOfMinSecond == s.index(i)[0] && 
    (forall |j: int| 0 <= j < s.len() ==> s.index(i)[1] <= s.index(j)[1])
{
    0
}

}