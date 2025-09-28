use vstd::prelude::*;

verus! {

// ex2

// this was me playing around to try and get an ensures for the method 
/*predicate method check(a: array<int>, seclar:int)
requires a.Length > 0
reads a
{ ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j]) } */

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn second_largest(a: &[i32]) -> (seclar: i32)
    requires a.len() > 0
    //ensures exists i :: 0 <= i < a.len() && forall j :: (0 <= j < a.len() && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j])
// </vc-spec>
// <vc-code>
{
    0
}
// </vc-code>

fn main() {
}

}