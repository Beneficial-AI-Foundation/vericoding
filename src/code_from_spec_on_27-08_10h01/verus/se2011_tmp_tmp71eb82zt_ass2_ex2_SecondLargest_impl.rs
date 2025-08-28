use vstd::prelude::*;

verus! {

// ex2

// this was me playing around to try and get an ensures for the method 
/*predicate method check(a: array<int>, seclar:int)
requires a.Length > 0
reads a
{ ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j]) } */

// <vc-helpers>
spec fn is_max(a: &[i32], max_idx: int) -> bool {
    0 <= max_idx < a.len() &&
    forall|j: int| 0 <= j < a.len() ==> a[max_idx] >= a[j]
}

spec fn is_second_largest(a: &[i32], second: i32) -> bool {
    exists|max_idx: int| #![auto] {
        &&& is_max(a, max_idx)
        &&& (forall|j: int| 0 <= j < a.len() && j != max_idx ==> second >= a[j])
        &&& second <= a[max_idx]
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn second_largest(a: &[i32]) -> (seclar: i32)
    requires a.len() > 0
    //ensures exists i :: 0 <= i < a.len() && forall j :: (0 <= j < a.len() && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j])
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut max = a[0];
    let mut second = a[0];
    let mut i = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            max >= second,
            forall|k: int| 0 <= k < i ==> max >= a[k],
            forall|k: int| 0 <= k < i && a[k] != max ==> second >= a[k],
            second <= max
        decreases a.len() - i
    {
        if a[i] > max {
            second = max;
            max = a[i];
        } else if a[i] > second {
            second = a[i];
        }
        i += 1;
    }
    
    second
}
// </vc-code>

fn main() {
}

}