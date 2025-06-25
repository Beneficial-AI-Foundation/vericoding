// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
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