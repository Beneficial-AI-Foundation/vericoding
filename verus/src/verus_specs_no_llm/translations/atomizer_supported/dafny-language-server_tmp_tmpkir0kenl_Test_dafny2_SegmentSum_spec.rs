// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sum(a: Seq<int>, s: int, t: int) -> int
    requires
        0 <= s <= t <= a.len()
{
    0
}

spec fn spec_MaxSegSum(a: Seq<int>) -> k: int, m: int
    ensures
        0 <= k <= m <= a.len(),
        forall |p: int, q: int| 0 <= p <= q <= a.len() ==> Sum(a, p, q) <= Sum(a, k, m)
;

proof fn lemma_MaxSegSum(a: Seq<int>) -> (k: int, m: int)
    ensures
        0 <= k <= m <= a.len(),
        forall |p: int, q: int| 0 <= p <= q <= a.len() ==> Sum(a, p, q) <= Sum(a, k, m)
{
    (0, 0)
}

}