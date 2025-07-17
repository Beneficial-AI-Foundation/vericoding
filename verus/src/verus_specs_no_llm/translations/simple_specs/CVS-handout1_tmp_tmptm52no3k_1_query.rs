// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sum(a: Vec<int>, i: int, j: int) -> int
  reads a
    requires
        0 <= i <= j <= a.len()
{
    0
}

spec fn spec_query(a: Vec<int>, i: int, j: int) -> res:int
    requires
        0 <= i <= j <= a.len()
    ensures
        res == sum(a, i, j)
;

proof fn lemma_query(a: Vec<int>, i: int, j: int) -> (res: int)
    requires
        0 <= i <= j <= a.len()
    ensures
        res == sum(a, i, j)
{
    0
}

}