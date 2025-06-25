// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn FindMedian(a: Vec<int>, b: Vec<int>) -> (median: int)
    requires a != null and b != null,
             a.len() == b.len(),
             a.len() > 0,
             forall|i: int| 0 <= i < a.len() - 1 ==> a[i] <= a[i + 1],
             forall|i: int| 0 <= i < b.len() - 1 ==> b[i] <= b[i + 1]
    ensures median == if (a.len() % 2 == 0) then (a[a.len() / 2 - 1] + b[0]) / 2 else a[a.len() / 2]
{
}

}