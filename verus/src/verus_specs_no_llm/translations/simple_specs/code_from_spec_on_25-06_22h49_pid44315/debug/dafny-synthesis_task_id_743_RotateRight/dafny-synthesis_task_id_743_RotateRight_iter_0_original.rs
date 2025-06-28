// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn RotateRight(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires
        n >= 0
    ensures
        r.len() == l.len(),
        forall i :: 0 <= i < l.len() ==> r.spec_index(i) == l.spec_index((i - n + l.len()) % l.len())
{
    return Seq::empty();
}

}