// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_arrayUpToN(n: int) -> a: array<int>
    requires
        n >= 0
    ensures
        a.len() == n,
        forall |j: int| 0 < j < n ==> a.index(j) >= 0,
        forall |j: int, k: int| 0 <= j <= k < n ==> a.index(j) <= a.index(k)
;

proof fn lemma_arrayUpToN(n: int) -> (a: Vec<int>)
    requires
        n >= 0
    ensures
        a.len() == n,
        forall |j: int| 0 < j < n ==> a.index(j) >= 0,
        forall |j: int, k: int| 0 <= j <= k < n ==> a.index(j) <= a.index(k)
{
    Vec::new()
}

}