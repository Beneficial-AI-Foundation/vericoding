use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn max_in_range(a: &[i32], start: int, end: int) -> i32
    recommends 0 <= start < end <= a.len()
    decreases end - start
{
    if start + 1 == end {
        a[start]
    } else {
        if a[start] >= max_in_range(a, start + 1, end) {
            a[start]
        } else {
            max_in_range(a, start + 1, end)
        }
    }
}

proof fn max_in_range_properties(a: &[i32], start: int, end: int)
    requires 0 <= start < end <= a.len()
    ensures 
        forall|i: int| start <= i < end ==> a[i] <= max_in_range(a, start, end),
        exists|i: int| start <= i < end && a[i] == max_in_range(a, start, end)
    decreases end - start
{
    if start + 1 == end {
        // Base case: single element
    } else {
        max_in_range_properties(a, start + 1, end);
        // The recursive case follows from the definition
    }
}

proof fn find_first_exceeding_helper(a: &[i32], max_val: i32, start: int, target: int) 
    requires 
        0 <= start <= target < a.len(),
        a[target] > max_val
    ensures
        exists|i: int| start <= i < a.len() && a[i] > max_val
{
    // Since a[target] > max_val and start <= target, we have our witness
}

fn compute_max_in_range(a: &[i32], start: usize, end: usize) -> (result: i32)
    requires 
        start < end <= a.len(),
        end <= a.len()
    ensures
        forall|i: int| start <= i < end ==> a[i] <= result,
        exists|i: int| start <= i < end && a[i] == result,
        result == max_in_range(a, start as int, end as int)
    decreases end - start
{
    if start + 1 == end {
        a[start]
    } else {
        let rest_max = compute_max_in_range(a, start + 1, end);
        if a[start] >= rest_max {
            a[start]
        } else {
            rest_max
        }
    }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    proof {
        max_in_range_properties(a, 0, x as int);
    }
    
    let ghost max_val = max_in_range(a, 0, x as int);
    let ghost_max = Ghost(max_val);
    let max_val_exec = compute_max_in_range(a, 0, x);
    
    // Find first element from position x onwards that exceeds max_val
    let mut i = x;
    while i < a.len() - 1
        invariant 
            x <= i < a.len(),
            forall|j: int| x <= j < i ==> a[j] <= max_val,
            max_val == max_in_range(a, 0, x as int),
            forall|k: int| 0 <= k < x ==> a[k] <= max_val,
            exists|k: int| 0 <= k < x && a[k] == max_val,
            max_val_exec == max_val
    {
        if a[i] > max_val_exec {
            proof {
                // Prove that all elements before i are <= max_val
                assert(forall|j: int| 0 <= j < i ==> a[j] < a[i as int]);
            }
            return (ghost_max, i);
        }
        i += 1;
    }
    
    // If we reach here, all elements from x to len-2 are <= max_val
    // So we return the last index
    (ghost_max, a.len() - 1)
}
// </vc-code>

fn main() {
}

}