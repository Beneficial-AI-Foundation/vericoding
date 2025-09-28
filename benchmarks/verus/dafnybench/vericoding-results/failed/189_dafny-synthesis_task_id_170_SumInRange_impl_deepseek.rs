use vstd::prelude::*;

verus! {

spec fn sum_to(a: Seq<int>, start: int, end: int) -> int
    recommends 
        0 <= start <= end <= a.len(),
    decreases end
    when 0 <= start <= end <= a.len()
{
    if start == end {
        0
    } else {
        sum_to(a, start, end - 1) + a[end - 1]
    }
}

// <vc-helpers>
proof fn sum_to_nonneg(a: Seq<int>, start: int, end: int, val: int)
    requires
        0 <= start <= end <= a.len(),
        forall|i: int| start <= i < end ==> a[i] >= 0,
        sum_to(a, start, end) == val,
    ensures
        val >= 0,
{
    if start < end {
        sum_to_nonneg(a, start, end - 1, sum_to(a, start, end - 1));
    }
}

spec fn all_nonnegative(a: Seq<int>, start: int, end: int) -> bool {
    forall|i: int| start <= i < end ==> a[i] >= 0
}

proof fn lemma_sum_to_recursive(a: Seq<int>, start: int, end: int)
    requires
        0 <= start <= end <= a.len(),
    ensures
        start < end ==> 
            sum_to(a, start, end) == sum_to(a, start, end - 1) + a[end - 1],
{
}

proof fn lemma_map_index(a: Seq<i32>, i: int) 
    requires
        0 <= i < a.len(),
    ensures
        a@.map(|j, v| v as int)[i] == a[i] as int,
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sum_in_range(a: &[i32], start: usize, end: usize) -> (sum: i32)
    requires 
        start <= end <= a.len(),
    ensures
        sum == sum_to(a@.map(|i, v| v as int), start as int, end as int),
// </vc-spec>
// <vc-code>
{
    let mut sum: i32 = 0;
    let mut idx: usize = start;
    
    while idx < end
        invariant
            idx <= end,
            sum == sum_to(a@.map(|i, v| v as int), start as int, idx as int),
        decreases end - idx
    {
        let old_idx = idx;
        sum = sum + a[idx];
        idx = idx + 1;
        
        proof {
            lemma_sum_to_recursive(a@.map(|i, v| v as int), start as int, idx as int);
            lemma_map_index(a@, old_idx as int);
            assert(a@.map(|i, v| v as int)[old_idx as int] == a[old_idx] as int);
            assert(sum_to(a@.map(|i, v| v as int), start as int, idx as int) == 
                   sum_to(a@.map(|i, v| v as int), start as int, old_idx as int) + a@.map(|i, v| v as int)[old_idx as int]);
            assert(sum == sum_to(a@.map(|i, v| v as int), start as int, old_idx as int) + (a[old_idx] as int));
        }
    }
    
    sum
}
// </vc-code>

fn main() {
}

}