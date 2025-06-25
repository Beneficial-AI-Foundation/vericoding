// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn LinearSearch(a: Vec<int>, e: int) -> (n: int)
    requires exists|i: int|0<=i<a.len() and a[i]==e
    ensures 0<=n<a.len() and a[n]==e,
            forall|k: int| 0 <= k < n ==> a[k]!=e
{
}

}