// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn longestZero(a: Vec<int>) -> sz: int, pos: int
    requires 1 <= a.len()
    ensures 0 <= sz <= a.len(),
            0 <= pos < a.len(),
            pos + sz <= a.len(),
            forall i:int  :: pos <= i < pos + sz ==> a[i] == 0,
            forall|i: int, j: int| (0 <= i < j < a.len() and getSize(i, j) > sz) ==> exists|k: int| i <= k <= j and a[k] != 0
{
}

}