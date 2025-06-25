// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn longestZero(a: Vec<int>) -> (sz: int, pos: int)
    requires
        1 <= a.len()
    ensures
        0 <= sz <= a.len(),
        0 <= pos < a.len(),
        pos + sz <= a.len(),
        forall i:int  :: pos <= i < pos + sz ==> a.spec_index(i) == 0,
        forall i,j :: (0 <= i < j < a.len() && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a.spec_index(k) != 0
{
    return (0, 0);
}

}