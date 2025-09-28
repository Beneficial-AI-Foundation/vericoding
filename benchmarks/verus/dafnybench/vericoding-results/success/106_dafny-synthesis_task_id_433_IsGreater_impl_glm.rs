use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_greater(n: i32, a: &[i32]) -> (result: bool)
    ensures 
        result ==> forall|i: int| 0 <= i < a.len() ==> n > a[i],
        !result ==> exists|i: int| 0 <= i < a.len() && n <= a[i],
// </vc-spec>
// <vc-code>
{
    for i in 0..a.len()
        invariant forall|k: int| 0 <= k < i ==> a@[k] < n
    {
        if a[i] >= n {
            return false;
        }
    }
    return true;
}
// </vc-code>

fn main() {
}

}