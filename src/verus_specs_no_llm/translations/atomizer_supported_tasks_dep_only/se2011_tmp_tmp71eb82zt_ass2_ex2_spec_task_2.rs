// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn check(a: Vec<int>, seclar: int)
requires a.Length > 0
reads a
{ ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j]) } */

// SPEC 
// ex2

// this was me playing around to try and get an ensures for the method 

method SecondLargest(a:array<int>) -> (seclar: int)
    requires a.len() > 0
reads a,
             a.len() > 0
//
    ensures exists|i: int| 0 <= i < a.len() and forall|j: int| (0 <= j < a.len() and j != i) ==> (a[i] >= a[j]) and (seclar <= a[i]) and ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j]) } */

// SPEC 
// ex2

// this was me playing around to try and get an,
            for the method 

method SecondLargest(a:array<int>) returns (seclar:int),
            exists|i: int| 0 <= i < a.len() and forall|j: int| (0 <= j < a.len() and j != i) ==> (a[i] >= a[j]) and (seclar <= a[i]) and ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j])
{
}

}