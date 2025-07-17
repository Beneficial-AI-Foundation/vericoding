// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_SearchRecursive(a: Seq<int>, i: int, j: int, x: int) -> k: int
    requires
        0 <= i <= j <= a.len()
    ensures
        i <= k < j || k == -1,
        k != -1 ==> a.index(k) == x,
        k != -1 ==> forall r | k < r < j :: a.index(r) != x,
        k == -1 ==> forall r | i <= r < j :: a.index(r) != x
;

proof fn lemma_SearchRecursive(a: Seq<int>, i: int, j: int, x: int) -> (k: int)
    requires
        0 <= i <= j <= a.len()
    ensures
        i <= k < j || k == -1,
        k != -1 ==> a.index(k) == x,
        k != -1 ==> forall r | k < r < j :: a.index(r) != x,
        k == -1 ==> forall r | i <= r < j :: a.index(r) != x
{
    0
}

}