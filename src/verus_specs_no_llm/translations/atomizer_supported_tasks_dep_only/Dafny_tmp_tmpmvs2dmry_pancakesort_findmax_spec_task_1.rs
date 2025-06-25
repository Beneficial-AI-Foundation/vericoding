// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn findMax(a: Vec<int>, n: int) -> (r: int)
    requires a.len() > 0,
             0 < n <= a.len()
    ensures 0 <= r < n <= a.len();,
            forall|k: int| 0 <= k < n <= a.len() ==> a[r] >= a[k];,
            multiset(a[..]) == multiset(old(a[..]));
{
}

}