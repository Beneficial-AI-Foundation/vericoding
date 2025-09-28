use vstd::prelude::*;

verus! {

spec fn min(a: int, b: int) -> int 
{
    if a < b { a } else { b }
}

spec fn min_function(a: int, b: int) -> int 
{
    if a < b { a } else { b }
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min_array(a: &Vec<i32>) -> (m: i32)
    requires a.len() > 0
    ensures forall|k: int| 0 <= k < a.len() ==> m <= a[k]
    ensures exists|k: int| 0 <= k < a.len() && m == a[k]
// </vc-spec>
// <vc-code>
{
    let mut min_val = a[0];
    let mut min_idx: usize = 0;
    
    for i in 1..a.len()
        invariant
            0 <= min_idx < i,
            i <= a.len(),
            min_val == a[min_idx as int],
            forall|k: int| 0 <= k < i ==> min_val <= a[k],
    {
        if a[i] < min_val {
            min_val = a[i];
            min_idx = i;
        }
    }
    
    assert(min_idx < a.len());
    assert(min_val == a[min_idx as int]);
    assert(forall|k: int| 0 <= k < a.len() ==> min_val <= a[k]);
    
    min_val
}
// </vc-code>

fn main() {
}

}