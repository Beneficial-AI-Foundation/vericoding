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

fn SecondLargest(a: Vec<int>) -> (seclar: int)
    requires
        a.len() > 0
//
    ensures
        exists i :: 0 <= i < a.len() && forall j :: (0 <= j < a.len() && j != i) ==> (a.spec_index(i) >= a.spec_index(j)) && (seclar <= a.spec_index(i)) && ( if a.spec_index(j) != a.spec_index(i) then seclar >= a.spec_index(j) else seclar <= a.spec_index(j))
{
    return 0;
}

}