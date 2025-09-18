// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn max_array_precond(a: &Vec<i32>) -> bool {
    a.len() > 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max_array(a: &Vec<i32>) -> (result: i32)
    requires max_array_precond(a),
    ensures
        forall|k: int| 0 <= k < a.len() ==> result >= a[k],
        exists|k: int| 0 <= k < a.len() && result == a[k],
// </vc-spec>
// <vc-code>
{
    let mut max_val = a[0];
    let mut i = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> max_val >= a[k],
            exists|k: int| 0 <= k < i && max_val == a[k],
        decreases a.len() - i
    {
        if a[i] > max_val {
            max_val = a[i];
        }
        i += 1;
    }
    
    max_val
}
// </vc-code>

}
fn main() {}