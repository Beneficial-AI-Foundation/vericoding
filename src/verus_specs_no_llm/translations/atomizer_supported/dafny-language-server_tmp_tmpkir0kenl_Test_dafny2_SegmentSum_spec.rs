// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn MaxSegSum(a: Seq<int>) -> k: int, m: int
    ensures 0 <= k <= m <= a.len(),
            forall|p: int, q: int| 0 <= p <= q <= a.len() ==> Sum(a, p, q) <= Sum(a, k, m)
{
}

}