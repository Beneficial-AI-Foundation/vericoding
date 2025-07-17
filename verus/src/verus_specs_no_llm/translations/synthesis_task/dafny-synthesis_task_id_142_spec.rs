// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_CountIdenticalPositions(a: Seq<int>, b: Seq<int>, c: Seq<int>) -> count: int
    requires
        a.len() == b.len() && b.len() == c.len()
    ensures
        count >= 0,
        count ==  set i: int .len() 0 <= i < a.len() && a.index(i) == b.index(i) && b.index(i) == c.index(i)|
;

proof fn lemma_CountIdenticalPositions(a: Seq<int>, b: Seq<int>, c: Seq<int>) -> (count: int)
    requires
        a.len() == b.len() && b.len() == c.len()
    ensures
        count >= 0,
        count ==  set i: int .len() 0 <= i < a.len() && a.index(i) == b.index(i) && b.index(i) == c.index(i)|
{
    0
}

}