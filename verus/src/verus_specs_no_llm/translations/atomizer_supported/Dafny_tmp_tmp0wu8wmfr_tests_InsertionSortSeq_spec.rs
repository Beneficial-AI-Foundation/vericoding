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

spec fn IsSorted(s: Seq<int>) -> bool {
    forall p,q  0<=p<q<.len()s| :: s.spec_index(p)<=s.spec_index(q)
}

fn InsertionSort(s: Seq<int>) -> (r: Seq<int>)
    ensures
        multiset(r) == multiset(s),
        IsSorted(r)
{
    return Seq::empty();
}

}