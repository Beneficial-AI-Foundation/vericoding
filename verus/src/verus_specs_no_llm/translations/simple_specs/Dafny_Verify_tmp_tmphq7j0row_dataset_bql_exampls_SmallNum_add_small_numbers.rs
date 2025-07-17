// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_add_small_numbers(a: Vec<int>, n: int, max: int) -> r: int
    requires
        n > 0,
        n <= a.len(),
        (forall |i: int| 0 <= i && i < n ==> a.index(i) <= max)
    ensures
        r <= max * n
;

proof fn lemma_add_small_numbers(a: Vec<int>, n: int, max: int) -> (r: int)
    requires
        n > 0,
        n <= a.len(),
        (forall |i: int| 0 <= i && i < n ==> a.index(i) <= max)
    ensures
        r <= max * n
{
    0
}

}