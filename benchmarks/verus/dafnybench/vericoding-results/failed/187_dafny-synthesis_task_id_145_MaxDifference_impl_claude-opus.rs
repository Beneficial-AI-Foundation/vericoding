use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helper functions needed for this implementation
// </vc-helpers>

// <vc-spec>
fn max_difference(a: &[i32]) -> (diff: i32)
    requires a.len() > 1
    ensures forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] - a[j] <= diff
// </vc-spec>
// <vc-code>
{
    let mut max_val: int = a[0] as int;
    let mut min_val: int = a[0] as int;
    
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] as int <= max_val,
            forall|j: int| 0 <= j < i ==> min_val <= a[j] as int,
            forall|p: int, q: int| 0 <= p < i && 0 <= q < i ==> (a[p] as int) - (a[q] as int) <= max_val - min_val,
    {
        if a[i] as int > max_val {
            max_val = a[i] as int;
        }
        if a[i] as int < min_val {
            min_val = a[i] as int;
        }
        i = i + 1;
    }
    
    assert(forall|j: int| 0 <= j < a.len() ==> a[j] as int <= max_val);
    assert(forall|j: int| 0 <= j < a.len() ==> min_val <= a[j] as int);
    
    let diff_int = max_val - min_val;
    
    assert(forall|p: int, q: int| 0 <= p < a.len() && 0 <= q < a.len() ==> {
        (a[p] as int <= max_val && min_val <= a[q] as int) ==> (a[p] as int) - (a[q] as int) <= max_val - min_val
    });
    
    assert(forall|p: int, q: int| 0 <= p < a.len() && 0 <= q < a.len() ==> (a[p] as int) - (a[q] as int) <= diff_int);
    
    // Now we need to prove that diff_int fits in i32
    assert(min_val >= i32::MIN as int);
    assert(max_val <= i32::MAX as int);
    assert(diff_int >= 0);
    assert(diff_int <= (i32::MAX as int) - (i32::MIN as int));
    assert(diff_int <= i32::MAX as int);
    
    let diff = diff_int as i32;
    
    assert(forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] - a[j] <= diff);
    
    diff
}
// </vc-code>

fn main() {
}

}