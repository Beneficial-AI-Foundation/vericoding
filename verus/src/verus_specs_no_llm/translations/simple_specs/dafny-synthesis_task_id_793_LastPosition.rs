// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_LastPosition(arr: Vec<int>, elem: int) -> pos: int
    requires
        arr.len() > 0,
        forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr.index(i) <= arr.index(j)
    ensures
        pos == -1 | (0 <= pos < arr.len() && arr.index(pos) == elem && (pos <= arr.len() - 1 .len()| arr.index(pos + 1) > elem)),
        forall |i: int| 0 <= i < arr.len() ==> arr.index(i) == old(arr.index(i))
;

proof fn lemma_LastPosition(arr: Vec<int>, elem: int) -> (pos: int)
    requires
        arr.len() > 0,
        forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr.index(i) <= arr.index(j)
    ensures
        pos == -1 | (0 <= pos < arr.len() && arr.index(pos) == elem && (pos <= arr.len() - 1 .len()| arr.index(pos + 1) > elem)),
        forall |i: int| 0 <= i < arr.len() ==> arr.index(i) == old(arr.index(i))
{
    0
}

}