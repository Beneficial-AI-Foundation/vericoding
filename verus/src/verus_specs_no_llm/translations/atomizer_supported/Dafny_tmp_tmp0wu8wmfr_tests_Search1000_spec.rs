// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Is2Pow(n: int) -> bool {
    if n < 1 then
        false
    else if n == 1 then
        true
    else
        n%2 == 0 && Is2Pow(n/2)
}

spec fn spec_Search1000(a: Vec<int>, x: int) -> k: int
    requires
        a.len() >= 1000,
        forall p,q | 0 <= p < q < 1000 :: a.index(p) <= a.index(q)
    ensures
        0 <= k <= 1000,
        forall r | 0 <= r < k :: a.index(r) < x,
        forall r | k <= r < 1000 :: a.index(r) >= x
;

proof fn lemma_Search1000(a: Vec<int>, x: int) -> (k: int)
    requires
        a.len() >= 1000,
        forall p,q | 0 <= p < q < 1000 :: a.index(p) <= a.index(q)
    ensures
        0 <= k <= 1000,
        forall r | 0 <= r < k :: a.index(r) < x,
        forall r | k <= r < 1000 :: a.index(r) >= x
{
    0
}

}