// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_SecondLargest(a: Vec<int>) -> seclar:int
    requires
        a.len() > 0
//
    ensures
        exists |i: int| 0 <= i < a.len() && forall |j: int| (0 <= j < a.len() && j != i) ==> (a.index(i) >= a.index(j)) && (seclar <= a.index(i)) && ( if a.index(j) != a.index(i) then seclar >= a.index(j) else seclar <= a.index(j))
;

proof fn lemma_SecondLargest(a: Vec<int>) -> (seclar: int)
    requires
        a.len() > 0
//
    ensures
        exists |i: int| 0 <= i < a.len() && forall |j: int| (0 <= j < a.len() && j != i) ==> (a.index(i) >= a.index(j)) && (seclar <= a.index(i)) && ( if a.index(j) != a.index(i) then seclar >= a.index(j) else seclar <= a.index(j))
{
    0
}

}