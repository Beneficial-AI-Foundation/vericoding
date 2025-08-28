use vstd::prelude::*;

verus! {

// Two-state predicate for checking if multiset is preserved
spec fn preserved(a_old: Seq<i32>, a_new: Seq<i32>, left: nat, right: nat) -> bool
    recommends left <= right <= a_old.len() && a_old.len() == a_new.len()
{
    a_old.subrange(left as int, right as int).to_multiset() == a_new.subrange(left as int, right as int).to_multiset()
}

// Predicate for checking if array slice is ordered
spec fn ordered(a: Seq<i32>, left: nat, right: nat) -> bool
    recommends left <= right <= a.len()
{
    forall|i: int| #![trigger a[i]] left < i < right ==> a[i-1] <= a[i]
}

// Two-state predicate for sorted array
spec fn sorted(a_old: Seq<i32>, a_new: Seq<i32>) -> bool
    recommends a_old.len() == a_new.len()
{
    ordered(a_new, 0, a_new.len() as nat) && preserved(a_old, a_new, 0, a_old.len() as nat)
}

// <vc-helpers>
proof fn lemma_swap_preserves_multiset(a: Seq<i32>, i: nat, j: nat)
    requires i < a.len() && j < a.len()
    ensures a.to_multiset() == a.update(i as int, a[j as int]).update(j as int, a[i as int]).to_multiset()
{
}

proof fn lemma_preserved_transitive(a: Seq<i32>, b: Seq<i32>, c: Seq<i32>, left: nat, right: nat)
    requires a.len() == b.len() == c.len()
    requires preserved(a, b, left, right)
    requires preserved(b, c, left, right)
    ensures preserved(a, c, left, right)
{
}

proof fn lemma_preserved_outside_unchanged(a: Seq<i32>, b: Seq<i32>, left: nat, right: nat, full_left: nat, full_right: nat)
    requires a.len() == b.len()
    requires full_left <= left <= right <= full_right <= a.len()
    requires forall|i: int| full_left <= i < full_right && !(left <= i < right) ==> a[i] == b[i]
    requires preserved(a, b, left, right)
    ensures preserved(a, b, full_left, full_right)
{
}

proof fn lemma_ordered_extend(a: Seq<i32>, left: nat, right: nat)
    requires left < right <= a.len()
    requires ordered(a, left, right)
    requires right == a.len() || a[(right-1) as int] <= a[right as int]
    ensures ordered(a, left, right + 1)
{
}

proof fn lemma_swap_maintains_order(a: Seq<i32>, i: usize, min_idx: usize)
    requires i < a.len() && min_idx < a.len()
    requires ordered(a, 0, i)
    requires forall|j: int| i <= j < a.len() ==> a[min_idx as int] <= a[j]
    requires forall|j: int, k: int| 0 <= j < i && i <= k < a.len() ==> a[j] <= a[k]
    ensures ordered(a.update(i as int, a[min_idx as int]).update(min_idx as int, a[i as int]), 0, i + 1)
{
}

proof fn lemma_swap_maintains_partition(a: Seq<i32>, i: usize, min_idx: usize)
    requires i < a.len() && min_idx < a.len() && i <= min_idx
    requires forall|j: int| i <= j < a.len() ==> a[min_idx as int] <= a[j]
    requires forall|j: int, k: int| 0 <= j < i && i <= k < a.len() ==> a[j] <= a[k]
    ensures forall|j: int, k: int| 0 <= j <= i && (i + 1) <= k < a.len() ==> 
        a.update(i as int, a[min_idx as int]).update(min_idx as int, a[i as int])[j] <= 
        a.update(i as int, a[min_idx as int]).update(min_idx as int, a[i as int])[k]
{
}

fn find_min_index(a: &Vec<i32>, start: usize, end: usize) -> (min_idx: usize)
    requires start < end <= a.len()
    ensures start <= min_idx < end
    ensures forall|j: int| start <= j < end ==> a@[min_idx as int] <= a@[j]
{
    let mut min_idx = start;
    let mut i = start + 1;
    
    while i < end
        invariant start <= min_idx < i <= end
        invariant forall|j: int| start <= j < i ==> a@[min_idx as int] <= a@[j]
    {
        if a[i] < a[min_idx] {
            min_idx = i;
        }
        i = i + 1;
    }
    
    min_idx
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures sorted(old(a)@, a@)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let n = a.len();
    let mut i = 0;
    
    while i < n
        invariant i <= n
        invariant ordered(a@, 0, i)
        invariant preserved(old(a)@, a@, 0, n)
        invariant forall|j: int, k: int| 0 <= j < i && i <= k < n ==> a@[j] <= a@[k]
    {
        if i < n {
            let min_idx = find_min_index(a, i, n);
            
            if min_idx != i {
                let old_a = a@;
                a.swap(i, min_idx);
                
                proof {
                    lemma_swap_preserves_multiset(old_a, i, min_idx);
                    lemma_preserved_transitive(old(a)@, old_a, a@, 0, n);
                    lemma_swap_maintains_order(old_a, i, min_idx);
                    lemma_swap_maintains_partition(old_a, i, min_idx);
                }
            }
        }
        
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}