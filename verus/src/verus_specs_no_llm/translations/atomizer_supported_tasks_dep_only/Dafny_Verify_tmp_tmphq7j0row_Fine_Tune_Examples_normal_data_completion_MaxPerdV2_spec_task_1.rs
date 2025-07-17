// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn contains(v: int, a: Vec<int>, n: int) -> bool
reads a
    requires
        n <= a.len()
{
    0
}

spec fn spec_max(a: Vec<int>, n: int) -> max: int
    requires
        0 < n <= a.len()
    ensures
        is_max(max, a, n)
;

proof fn lemma_max(a: Vec<int>, n: int) -> (max: int)
    requires
        0 < n <= a.len()
    ensures
        is_max(max, a, n)
{
    0
}

}