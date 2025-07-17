// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(s: Seq<int>) -> bool
{
    false
}

spec fn spec_copyArr(a: Vec<int>, l: int, r: int) -> ret : array<int>
    requires
        0 <= l < r <= a.len()
    ensures
        ret.index(..) == a.index(l..r)
;

proof fn lemma_copyArr(a: Vec<int>, l: int, r: int) -> (ret: Vec<int>)
    requires
        0 <= l < r <= a.len()
    ensures
        ret.index(..) == a.index(l..r)
{
    Vec::new()
}

}