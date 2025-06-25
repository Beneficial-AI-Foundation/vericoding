// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn quickSort(Seq: Seq<int>) -> (Seq': Seq<int>)
    ensures
        multiset(Seq) == multiset(Seq')
{
    return Seq::empty();
}

}