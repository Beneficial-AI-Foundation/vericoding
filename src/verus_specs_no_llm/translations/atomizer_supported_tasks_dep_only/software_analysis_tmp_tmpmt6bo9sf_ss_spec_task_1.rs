// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn find_min_index(a: Vec<int>, s: int, e: int) -> (min_i: int)
    requires a.len() > 0,
             0 <= s < a.len(),
             e <= a.len(),
             e > s
    ensures min_i >= s,
            min_i < e,
            forall k: int :: s <= k < e ==> a[min_i] <= a[k]
{
}

}