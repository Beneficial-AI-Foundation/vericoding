use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
{
    &&& 0 <= i <= j <= a.len()
    &&& forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn min_index_in_range(a: Seq<int>, start: int, end: int) -> int
    recommends 0 <= start < end <= a.len()
{
    if start + 1 == end { start }
    else if a[start] <= a[min_index_in_range(a, start + 1, end)] { start }
    else { min_index_in_range(a, start + 1, end) }
}

proof fn min_index_properties(a: Seq<int>, start: int, end: int)
    requires 0 <= start < end <= a.len()
    ensures 
        start <= min_index_in_range(a, start, end) < end,
        forall|i: int| start <= i < end ==> a[min_index_in_range(a, start, end)] <= a[i]
    decreases end - start
{
    if start + 1 == end {
    } else {
        min_index_properties(a, start + 1, end);
        let min_rest = min_index_in_range(a, start + 1, end);
        if a[start] <= a[min_rest] {
        } else {
        }
    }
}

fn find_min_index(a: &Vec<int>, start: usize, end: usize) -> (result: usize)
    requires start < end <= a.len()
    ensures 
        start <= result < end,
        forall|i: int| start <= i < end ==> #[trigger] a@[result as int] <= a@[i],
        result == min_index_in_range(a@, start as int, end as int)
{
    let mut min_idx = start;
    let mut i = start + 1;
    
    while i < end
        invariant
            start <= min_idx < i <= end,
            forall|j: int| start <= j < i ==> #[trigger] a@[min_idx as int] <= a@[j],
            min_idx == min_index_in_range(a@, start as int, i as int)
    {
        if a[i] < a[min_idx] {
            min_idx = i;
        }
        
        proof {
            if a@[i as int] < a@[min_idx as int] {
                assert(forall|j: int| start <= j < (i + 1) as int ==> #[trigger] a@[i as int] <= a@[j]);
            } else {
                assert(forall|j: int| start <= j < (i + 1) as int ==> #[trigger] a@[min_idx as int] <= a@[j]);
            }
        }
        
        i += 1;
    }
    
    proof {
        min_index_properties(a@, start as int, end as int);
    }
    
    min_idx
}

proof fn swap_preserves_multiset<T>(v1: Seq<T>, v2: Seq<T>, i: int, j: int, start: int, end: int)
    requires 
        0 <= start <= end <= v1.len() == v2.len(),
        start <= i < end,
        start <= j < end,
        v2 == v1.update(i, v1[j]).update(j, v1[i])
    ensures v1.subrange(start, end).to_multiset() == v2.subrange(start, end).to_multiset()
{
}

proof fn swap_preserves_sorted_prefix(a_old: Seq<int>, a_new: Seq<int>, sorted_end: int, swap_i: int, swap_j: int)
    requires 
        0 <= sorted_end <= swap_i,
        swap_i < swap_j < a_old.len(),
        a_old.len() == a_new.len(),
        a_new == a_old.update(swap_i, a_old[swap_j]).update(swap_j, a_old[swap_i]),
        sorted_seg(a_old, 0, sorted_end),
        forall|k: int| sorted_end <= k < swap_j ==> a_old[sorted_end] <= a_old[k]
    ensures 
        sorted_seg(a_new, 0, sorted_end + 1),
        forall|k: int| sorted_end + 1 <= k < swap_j ==> a_new[sorted_end] <= a_new[k]
{
}
// </vc-helpers>

// <vc-spec>
fn sel_sort(a: &mut Vec<int>, c: usize, f: usize)
    requires 
        c <= f <= old(a).len(),
    ensures 
        sorted_seg(a@, c as int, f as int),
        a.len() == old(a).len(),
        a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
        a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
        a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
// </vc-spec>
// <vc-code>
{
    let mut i = c;
    
    while i < f
        invariant
            c <= i <= f,
            a.len() == old(a).len(),
            sorted_seg(a@, c as int, i as int),
            forall|j: int, k: int| c <= j < i && i <= k < f ==> #[trigger] a@[j] <= a@[k],
            a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
            a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
            a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int)
    {
        if i + 1 < f {
            let min_idx = find_min_index(a, i, f);
            
            proof {
                min_index_properties(a@, i as int, f as int);
            }
            
            if min_idx != i {
                let old_a = a@;
                let temp = a[i as int];
                a.set(i as int, a[min_idx as int]);
                a.set(min_idx as int, temp);
                
                proof {
                    swap_preserves_multiset(old_a, a@, i as int, min_idx as int, c as int, f as int);
                    swap_preserves_sorted_prefix(old_a, a@, i as int, i as int, min_idx as int);
                }
            }
        }
        
        i += 1;
    }
}
// </vc-code>

fn main() {}

}