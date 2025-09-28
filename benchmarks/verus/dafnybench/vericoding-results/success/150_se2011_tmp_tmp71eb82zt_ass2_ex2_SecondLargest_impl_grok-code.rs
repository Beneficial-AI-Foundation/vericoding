use vstd::prelude::*;

verus! {

// ex2

// this was me playing around to try and get an ensures for the method 
/*predicate method check(a: array<int>, seclar:int)
requires a.Length > 0
reads a
{ ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j]) } */

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn second_largest(a: &[i32]) -> (seclar: i32)
    requires a.len() > 0
    //ensures exists i :: 0 <= i < a.len() && forall j :: (0 <= j < a.len() && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j])
// </vc-spec>
// <vc-code>
{
    if a.len() == 1 {
        a[0]
    } else {
        let mut max1 = if a[0] > a[1] { a[0] } else { a[1] };
        let mut max2 = if a[0] > a[1] { a[1] } else { a[0] };
        for i in 2..a.len() {
            if a[i] > max1 {
                max2 = max1;
                max1 = a[i];
            } else if a[i] > max2 {
                max2 = a[i];
            }
        }
        max2
    }
}
// </vc-code>

fn main() {
}

}