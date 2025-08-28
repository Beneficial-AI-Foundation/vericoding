use vstd::prelude::*;

verus! {

spec fn sorted(a: &Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

spec fn sorted_range(a: &Vec<i32>, end: int) -> bool {
    forall|i: int, j: int| 0 <= i < j < end ==> a[i] <= a[j]
}

fn look_for_min(a: &Vec<i32>, i: usize) -> (m: usize)
    requires 
        0 <= i < a.len()
    ensures 
        i <= m < a.len(),
        forall|k: int| i <= k < a.len() ==> a[k as int] >= a[m as int]
{
    assume(false);
    i // placeholder return
}

// <vc-helpers>
proof fn sorted_range_implies_sorted(a: &Vec<i32>)
    ensures sorted_range(a, a.len() as int) == sorted(a)
{
}

proof fn sorted_range_extend(a: &Vec<i32>, end: int, new_end: int)
    requires 
        0 <= end <= new_end <= a.len(),
        sorted_range(a, end),
        forall|k: int| 0 <= k < end ==> a[k] <= a[end]
    ensures sorted_range(a, end + 1)
{
}

proof fn insertion_preserves_sorted_range(a: &Vec<i32>, old_a: &Vec<i32>, pos: int, end: int)
    requires
        0 <= pos < end <= a.len(),
        a.len() == old_a.len(),
        sorted_range(old_a, pos),
        forall|k: int| 0 <= k < pos ==> a[k] <= a[pos],
        forall|k: int| 0 <= k <= pos ==> exists|j: int| 0 <= j < end && a[k] == old_a[j],
        forall|k: int| pos < k < a.len() ==> a[k] == old_a[k]
    ensures sorted_range(a, pos + 1)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn insertion_sort(a: &mut Vec<i32>)
    ensures sorted(a)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut i = 1;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            sorted_range(a, i as int)
        decreases a.len() - i
    {
        let key = a[i];
        let mut j = i;
        
        while j > 0 && a[j - 1] > key
            invariant
                0 <= j <= i,
                sorted_range(a, i as int),
                forall|k: int| j < k <= i ==> a[k] > key,
                forall|k: int| 0 <= k < j ==> a[k] <= key || k == j - 1
            decreases j
        {
            let prev_val = a[j - 1];
            a.set(j, prev_val);
            j -= 1;
        }
        
        a.set(j, key);
        
        proof {
            assert(sorted_range(a, (i + 1) as int));
        }
        
        i += 1;
    }
    
    proof {
        sorted_range_implies_sorted(a);
    }
}
// </vc-code>

fn main() {
}

}