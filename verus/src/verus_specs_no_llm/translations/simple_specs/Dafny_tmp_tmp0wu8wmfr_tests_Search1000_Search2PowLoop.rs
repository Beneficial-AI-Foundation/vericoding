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

spec fn spec_Search2PowLoop(a: Vec<int>, i: int, n: int, x: int) -> k: int
    requires
        0 <= i <= i+n <= a.len(),
        forall p,q | i <= p < q < i+n :: a.index(p) <= a.index(q),
        Is2Pow(n+1)
    ensures
        i <= k <= i+n,
        forall r | i <= r < k :: a.index(r) < x,
        forall r | k <= r < i+n :: a.index(r) >= x
;

proof fn lemma_Search2PowLoop(a: Vec<int>, i: int, n: int, x: int) -> (k: int)
    requires
        0 <= i <= i+n <= a.len(),
        forall p,q | i <= p < q < i+n :: a.index(p) <= a.index(q),
        Is2Pow(n+1)
    ensures
        i <= k <= i+n,
        forall r | i <= r < k :: a.index(r) < x,
        forall r | k <= r < i+n :: a.index(r) >= x
{
    0
}

}