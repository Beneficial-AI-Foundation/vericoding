// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn SearchLoop(a: Seq<int>, i: int, j: int, x: int) -> (k: int)
    requires 0 <= i <= j <= a.len();
    ensures i <= k < j or k == -1;,
            k != -1 ==> a[k] == x;,
            k != -1 ==> forall|r | k < r < j: int| a[r] != x;,
            k == -1 ==> forall|r | i <= r < j: int| a[r] != x;
{
}

}