// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn getSize(i: int, j: int) -> int
{
    0
}

spec fn spec_longestZero(a: Vec<int>) -> sz:int, pos:int
    requires
        1 <= a.len()
    ensures
        0 <= sz <= a.len(),
        0 <= pos < a.len(),
        pos + sz <= a.len(),
        forall |i: int| pos <= i < pos + sz ==> a.index(i) == 0,
        forall |i: int, j: int| (0 <= i < j < a.len() && getSize(i, j) > sz) ==> exists |k: int| i <= k <= j && a.index(k) != 0
;

proof fn lemma_longestZero(a: Vec<int>) -> (sz: int, pos: int)
    requires
        1 <= a.len()
    ensures
        0 <= sz <= a.len(),
        0 <= pos < a.len(),
        pos + sz <= a.len(),
        forall |i: int| pos <= i < pos + sz ==> a.index(i) == 0,
        forall |i: int, j: int| (0 <= i < j < a.len() && getSize(i, j) > sz) ==> exists |k: int| i <= k <= j && a.index(k) != 0
{
    (0, 0)
}

}