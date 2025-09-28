use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_max_diff_property(a: &[i32], max_val: i32, min_val: i32)
    requires 
        a.len() > 1,
        forall|k: int| 0 <= k < a.len() ==> a[k] <= max_val,
        forall|k: int| 0 <= k < a.len() ==> a[k] >= min_val,
        exists|i: int| 0 <= i < a.len() && a[i] == max_val,
        exists|j: int| 0 <= j < a.len() && a[j] == min_val
    ensures 
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] - a[j] <= max_val - min_val
{
    assert forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() implies a[i] - a[j] <= max_val - min_val by {
        assert(a[i] <= max_val);
        assert(a[j] >= min_val);
    }
}

proof fn lemma_diff_in_bounds(max_val: i32, min_val: i32)
    requires max_val >= min_val
    ensures max_val - min_val >= 0
    ensures (max_val as i64) - (min_val as i64) <= i32::MAX as i64
{
    if min_val >= 0 {
        assert(max_val - min_val <= max_val);
        assert(max_val <= i32::MAX);
    } else {
        assert(max_val >= i32::MIN);
        assert(min_val >= i32::MIN);
        assert((max_val as i64) - (min_val as i64) <= (i32::MAX as i64) - (i32::MIN as i64));
        assert((i32::MAX as i64) - (i32::MIN as i64) <= i32::MAX as i64);
    }
}
// </vc-helpers>

// <vc-spec>
fn max_difference(a: &[i32]) -> (diff: i32)
    requires a.len() > 1
    ensures forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] - a[j] <= diff
// </vc-spec>
// <vc-code>
{
    let mut max_val = a[0];
    let mut min_val = a[0];
    
    let mut idx = 1;
    while idx < a.len()
        invariant
            1 <= idx <= a.len(),
            forall|k: int| 0 <= k < idx ==> a[k] <= max_val,
            forall|k: int| 0 <= k < idx ==> a[k] >= min_val,
            exists|i: int| 0 <= i < idx && a[i] == max_val,
            exists|j: int| 0 <= j < idx && a[j] == min_val
        decreases a.len() - idx
    {
        if a[idx] > max_val {
            max_val = a[idx];
        }
        if a[idx] < min_val {
            min_val = a[idx];
        }
        idx += 1;
    }
    
    proof {
        lemma_max_diff_property(a, max_val, min_val);
        lemma_diff_in_bounds(max_val, min_val);
    }
    
    max_val - min_val
}
// </vc-code>

fn main() {
}

}