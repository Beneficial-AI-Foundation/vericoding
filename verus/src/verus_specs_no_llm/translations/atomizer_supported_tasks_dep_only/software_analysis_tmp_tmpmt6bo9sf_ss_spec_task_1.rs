// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_find_min_index(a: Vec<int>, s: int, e: int) -> min_i: int
    requires
        a.len() > 0,
        0 <= s < a.len(),
        e <= a.len(),
        e > s
    ensures
        min_i >= s,
        min_i < e,
        forall |k: int| s <= k < e ==> a.index(min_i) <= a.index(k)
;

proof fn lemma_find_min_index(a: Vec<int>, s: int, e: int) -> (min_i: int)
    requires
        a.len() > 0,
        0 <= s < a.len(),
        e <= a.len(),
        e > s
    ensures
        min_i >= s,
        min_i < e,
        forall |k: int| s <= k < e ==> a.index(min_i) <= a.index(k)
{
    0
}

}