// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_LinearSearch(a: Vec<int>, e: int) -> n:int
    ensures
        0<=n<=a.len(),
        n==a.len() || a.index(n)==e,
        forall |i: int|0<=i < n ==> e!=a.index(i)
;

proof fn lemma_LinearSearch(a: Vec<int>, e: int) -> (n: int)
    ensures
        0<=n<=a.len(),
        n==a.len() || a.index(n)==e,
        forall |i: int|0<=i < n ==> e!=a.index(i)
{
    0
}

}