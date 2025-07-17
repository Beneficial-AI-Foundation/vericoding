// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Power(base: int, exponent: int) -> int
    requires
        exponent >= 0
{
    0
}

spec fn spec_PowerOfListElements(l: Seq<int>, n: int) -> result: seq<int>
    requires
        n >= 0
    ensures
        result.len() == l.len(),
        forall |i: int| 0 <= i < l.len() ==> result.index(i) == Power(l.index(i), n)
;

proof fn lemma_PowerOfListElements(l: Seq<int>, n: int) -> (result: Seq<int>)
    requires
        n >= 0
    ensures
        result.len() == l.len(),
        forall |i: int| 0 <= i < l.len() ==> result.index(i) == Power(l.index(i), n)
{
    Seq::empty()
}

}