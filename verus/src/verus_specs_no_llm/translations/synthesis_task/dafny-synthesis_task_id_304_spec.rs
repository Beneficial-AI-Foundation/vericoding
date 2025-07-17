// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_ElementAtIndexAfterRotation(l: Seq<int>, n: int, index: int) -> element: int
    requires
        n >= 0,
        0 <= index < l.len()
    ensures
        element == l.index((index - n + l.len()) % l.len())
;

proof fn lemma_ElementAtIndexAfterRotation(l: Seq<int>, n: int, index: int) -> (element: int)
    requires
        n >= 0,
        0 <= index < l.len()
    ensures
        element == l.index((index - n + l.len()) % l.len())
{
    0
}

}