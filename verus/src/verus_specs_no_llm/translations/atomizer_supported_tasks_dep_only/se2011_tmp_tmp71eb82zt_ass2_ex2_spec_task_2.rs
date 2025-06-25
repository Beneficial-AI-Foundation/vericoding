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

fn check(a: Vec<int>, seclar: int)
requires a.Length > 0
reads a
{ ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j]) } */

// SPEC 
// ex2

// this was me playing around to try and get an ensures for the method 

method SecondLargest(a:array<int>) -> (seclar: int)
    requires
        a.len() > 0
reads a,
        a.len() > 0
//
    ensures
        exists i :: 0 <= i < a.len() && forall j :: (0 <= j < a.len() && j != i) ==> (a.spec_index(i) >= a.spec_index(j)) && (seclar <= a.spec_index(i)) && ( if a.spec_index(j) != a.spec_index(i) then seclar >= a.spec_index(j) else seclar <= a.spec_index(j)) } */

// SPEC 
// ex2

// this was me playing around to try && get an,
        for the method 

method SecondLargest(a:array<int>) returns (seclar:int),
        exists i :: 0 <= i < a.len() && forall j :: (0 <= j < a.len() && j != i) ==> (a.spec_index(i) >= a.spec_index(j)) && (seclar <= a.spec_index(i)) && ( if a.spec_index(j) != a.spec_index(i) then seclar >= a.spec_index(j) else seclar <= a.spec_index(j))
{
    return 0;
}

}