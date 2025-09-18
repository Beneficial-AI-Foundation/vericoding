// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn all_elements_equal<T>(a1: &Vec<T>, a2: &Vec<T>, start: int, end: int) -> bool
    where T: PartialEq<T>,
    requires 0 <= start <= end <= a1.len() && a1.len() == a2.len(),
{
    forall|i: int| start <= i < end ==> a1@[i] == a2@[i]
}
// </vc-helpers>

// <vc-spec>
fn array_equal<T>(a1: &Vec<T>, a2: &Vec<T>) -> (result: bool)
    where T: PartialEq<T>,
    requires a1.len() == a2.len(),
    ensures 
        result == true <==> (forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i]) &&
        (a1.len() == 0 ==> result == true) &&
        (exists|i: int| 0 <= i < a1.len() && !(a1[i] == a2[i]) ==> result == false)
// </vc-spec>
// <vc-code>
{
    if a1.len() == 0 {
        return true;
    }
    
    let mut i = 0;
    while i < a1.len()
        invariant 0 <= i <= a1.len(),
        invariant all_elements_equal(a1, a2, 0, i),
        decreases a1.len() - i,
    {
        if a1[i] != a2[i] {
            return false;
        }
        i += 1;
    }
    
    true
}
// </vc-code>

}
fn main() {}