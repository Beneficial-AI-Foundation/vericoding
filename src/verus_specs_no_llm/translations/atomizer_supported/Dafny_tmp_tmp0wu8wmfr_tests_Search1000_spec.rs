// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn Is2Pow(n: int) -> bool {
    if n < 1 then
        false
    else if n == 1 then
        true
    else
        n%2 == 0 and Is2Pow(n/2)
}

fn Search1000(a: Vec<int>, x: int) -> (k: int)
    requires a.len() >= 1000;,
             forall|p: int, q | 0 <= p < q < 1000: int| a[p] <= a[q];
    ensures 0 <= k <= 1000;,
            forall|r | 0 <= r < k: int| a[r] < x;,
            forall|r | k <= r < 1000: int| a[r] >= x;
{
}

}