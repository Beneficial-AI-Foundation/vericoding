// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn LastPosition(arr: Vec<int>, elem: int) -> (pos: int)
    requires
        arr.len() > 0,
        forall i, j :: 0 <= i < j < arr.len() ==> arr.spec_index(i) <= arr.spec_index(j)
    ensures
        pos == -1 | (0 <= pos < arr.len() && arr.spec_index(pos) == elem && (pos <= arr.len() - 1 .len()| arr.spec_index(pos + 1) > elem)),
        forall i :: 0 <= i < arr.len() ==> arr.spec_index(i) == old(arr.spec_index(i))
{
    return 0;
}

}