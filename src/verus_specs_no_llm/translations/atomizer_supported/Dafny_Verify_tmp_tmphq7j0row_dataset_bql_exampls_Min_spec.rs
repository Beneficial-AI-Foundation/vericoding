// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn min(a: Vec<int>, n: int) -> (min: int)
    requires 0 < n <= a.len();
    ensures (exists i : int :: 0 <= i and i < n and a[i] == min);,
            (forall i : int :: 0 <= i and i < n ==> a[i] >= min);
{
}

}