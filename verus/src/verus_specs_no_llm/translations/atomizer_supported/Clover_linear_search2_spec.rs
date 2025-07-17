// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_LinearSearch(a: Vec<int>, e: int) -> n:int
    requires
        exists |i: int|0<=i<a.len() && a.index(i)==e
    ensures
        0<=n<a.len() && a.index(n)==e,
        forall |k: int| 0 <= k < n ==> a.index(k)!=e
;

proof fn lemma_LinearSearch(a: Vec<int>, e: int) -> (n: int)
    requires
        exists |i: int|0<=i<a.len() && a.index(i)==e
    ensures
        0<=n<a.len() && a.index(n)==e,
        forall |k: int| 0 <= k < n ==> a.index(k)!=e
{
    0
}

}