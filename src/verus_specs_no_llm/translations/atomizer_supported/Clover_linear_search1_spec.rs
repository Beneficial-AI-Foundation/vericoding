// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn LinearSearch(a: Vec<int>, e: int) -> (n: int)
    ensures 0<=n<=a.len(),
            n==a.len() or a[n]==e,
            forall|i: int|0<=i < n ==> e!=a[i]
{
}

}