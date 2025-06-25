// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall i,j :: 0 <= i <= j < q.len() ==> q.spec_index(i) <= q.spec_index(j)
}

fn MergeSort(a: Vec<int>) -> (b: Vec<int>)
    ensures
        b.len() == a.len() && Sorted(b.spec_index(..)) && multiset(a.spec_index(..)) == multiset(b.spec_index(..))
{
    return Vec::new();
}

}