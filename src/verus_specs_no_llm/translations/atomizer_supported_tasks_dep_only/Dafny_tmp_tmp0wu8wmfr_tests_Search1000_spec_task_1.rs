// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Search1000(a: Vec<int>, x: int) -> (k: int)
    requires a.len() >= 1000;,
             forall|p: int, q | 0 <= p < q < 1000: int| a[p] <= a[q];
    ensures 0 <= k <= 1000;,
            forall|r | 0 <= r < k: int| a[r] < x;,
            forall|r | k <= r < 1000: int| a[r] >= x;
{
}

}