// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_findMax(a: Vec<int>, n: int) -> r:int
    requires
        a.len() > 0,
        0 < n <= a.len()
    ensures
        0 <= r < n <= a.len(),
        forall |k: int| 0 <= k < n <= a.len() ==> a.index(r) >= a.index(k),
        multiset(a.index(..)) == multiset(old(a.index(..)))
;

proof fn lemma_findMax(a: Vec<int>, n: int) -> (r: int)
    requires
        a.len() > 0,
        0 < n <= a.len()
    ensures
        0 <= r < n <= a.len(),
        forall |k: int| 0 <= k < n <= a.len() ==> a.index(r) >= a.index(k),
        multiset(a.index(..)) == multiset(old(a.index(..)))
{
    0
}

}