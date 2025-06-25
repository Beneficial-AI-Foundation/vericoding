// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn max(a: Vec<int>, b: Vec<int>, i: int, j: int) -> (m: int)
    requires 0 <= i < a.len(),
             0 <= j < b.len()
    ensures a[i] > b[j] ==> m == a[i],
            a[i] <= b[j] ==> m == b[j]
{
}

}