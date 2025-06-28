// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MaxSegSum(a: Seq<int>) -> (k: int, m: int)
    ensures
        0 <= k <= m <= a.len(),
        forall p,q :: 0 <= p <= q <= a.len() ==> Sum(a, p, q) <= Sum(a, k, m)
{
    return (0, 0);
}

}