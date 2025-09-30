use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
fn online_max(a: &[i32], x: usize) -> (result: (Ghost<i32>, usize))
    requires 
        1 <= x < a.len(),
        a.len() != 0,
    ensures
        x <= result.1 < a.len(),
        forall|i: int| 0 <= i < x ==> #[trigger] a[i] <= result.0@,
        exists|i: int| 0 <= i < x && #[trigger] a[i] == result.0@,
        x <= result.1 < a.len() - 1 ==> (forall|i: int| 0 <= i < result.1 ==> #[trigger] a[i] < a[result.1 as int]),
        (forall|i: int| x <= i < a.len() && #[trigger] a[i] <= result.0@) ==> result.1 == a.len() - 1
// </vc-spec>
// <vc-code>
{
    // First, find the maximum value in a[0..x]
    let mut max_val: i32 = a[0];
    let mut max_idx: usize = 0;
    
    let mut i: usize = 1;
    while i < x
        invariant
            1 <= i <= x,
            x < a.len(),
            0 <= max_idx < i,
            max_idx < a.len(),
            a[max_idx as int] == max_val,
            forall|j: int| 0 <= j < i ==> #[trigger] a[j] <= max_val,
            exists|j: int| 0 <= j < i && #[trigger] a[j] == max_val,
        decreases x - i,
    {
        assert(i < a.len());
        if a[i] > max_val {
            max_val = a[i];
            max_idx = i;
        }
        i = i + 1;
    }
    
    // After the loop, we have the maximum of a[0..x]
    assert(forall|j: int| 0 <= j < x ==> #[trigger] a[j] <= max_val);
    assert(exists|j: int| 0 <= j < x && #[trigger] a[j] == max_val);
    
    // Now find the first index >= x where a value exceeds max_val
    let mut stop_idx: usize = x;
    
    while stop_idx < a.len()
        invariant
            x <= stop_idx <= a.len(),
            forall|j: int| 0 <= j < x ==> #[trigger] a[j] <= max_val,
            exists|j: int| 0 <= j < x && #[trigger] a[j] == max_val,
            forall|j: int| x <= j < stop_idx ==> #[trigger] a[j] <= max_val,
        decreases a.len() - stop_idx,
    {
        if a[stop_idx] > max_val {
            assert(forall|j: int| 0 <= j < stop_idx ==> #[trigger] a[j] < a[stop_idx as int]) by {
                assert forall|j: int| 0 <= j < x implies #[trigger] a[j] < a[stop_idx as int] by {
                    assert(a[j] <= max_val);
                    assert(a[stop_idx as int] > max_val);
                }
                assert forall|j: int| x <= j < stop_idx implies #[trigger] a[j] < a[stop_idx as int] by {
                    assert(a[j] <= max_val);
                    assert(a[stop_idx as int] > max_val);
                }
            }
            return (Ghost(max_val), stop_idx);
        }
        stop_idx = stop_idx + 1;
    }
    
    // If we exit the loop, all elements from x onwards are <= max_val
    assert(stop_idx == a.len());
    assert(forall|j: int| x <= j < a.len() ==> #[trigger] a[j] <= max_val);
    assert(forall|j: int| 0 <= j < x ==> #[trigger] a[j] <= max_val);
    assert(exists|j: int| 0 <= j < x && #[trigger] a[j] == max_val);
    (Ghost(max_val), (a.len() - 1) as usize)
}
// </vc-code>

fn main() {
}

}