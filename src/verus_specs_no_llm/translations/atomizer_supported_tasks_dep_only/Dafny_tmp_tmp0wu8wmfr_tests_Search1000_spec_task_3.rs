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

fn Search2PowRecursive(a: Vec<int>, i: int, n: int, x: int) -> (k: int)
    requires 0 <= i <= i+n <= a.len();,
             forall|p: int, q | i <= p < q < i+n: int| a[p] <= a[q];,
             Is2Pow(n+1);
    ensures i <= k <= i+n;,
            forall|r | i <= r < k: int| a[r] < x;,
            forall|r | k <= r < i+n: int| a[r] >= x;
{
}

}