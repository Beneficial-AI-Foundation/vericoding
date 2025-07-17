// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_check(a: Vec<int>, seclar: int)
requires a.Length > 0
reads a
{ ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j]) } */

// SPEC 
// ex2

// this was me playing around to try and get an ensures for the method 

method SecondLargest(a:array<int>) -> seclar:int
    requires
        a.len() > 0
reads a,
        a.len() > 0
//
    ensures
        exists |i: int| 0 <= i < a.len() && forall |j: int| (0 <= j < a.len() && j != i) ==> (a.index(i) >= a.index(j)) && (seclar <= a.index(i)) && ( if a.index(j) != a.index(i) then seclar >= a.index(j) else seclar <= a.index(j)) } */

// SPEC 
// ex2

// this was me playing around to try && get an,
        for the method 

method SecondLargest(a:array<int>) returns (seclar:int),
        exists |i: int| 0 <= i < a.len() && forall |j: int| (0 <= j < a.len() && j != i) ==> (a.index(i) >= a.index(j)) && (seclar <= a.index(i)) && ( if a.index(j) != a.index(i) then seclar >= a.index(j) else seclar <= a.index(j))
;

proof fn lemma_check(a: Vec<int>, seclar: int)
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
        exists |i: int| 0 <= i < a.len() && forall |j: int| (0 <= j < a.len() && j != i) ==> (a.index(i) >= a.index(j)) && (seclar <= a.index(i)) && ( if a.index(j) != a.index(i) then seclar >= a.index(j) else seclar <= a.index(j)) } */

// SPEC 
// ex2

// this was me playing around to try && get an,
        for the method 

method SecondLargest(a:array<int>) returns (seclar:int),
        exists |i: int| 0 <= i < a.len() && forall |j: int| (0 <= j < a.len() && j != i) ==> (a.index(i) >= a.index(j)) && (seclar <= a.index(i)) && ( if a.index(j) != a.index(i) then seclar >= a.index(j) else seclar <= a.index(j))
{
    0
}

}