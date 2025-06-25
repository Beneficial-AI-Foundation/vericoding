// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn arrayUpToN(n: int) -> (a: Vec<int>)
    requires n >= 0
    ensures a.len() == n,
            forall|j: int| 0 < j < n ==> a[j] >= 0,
            forall j, k : int :: 0 <= j <= k < n ==> a[j] <= a[k]
{
}

}