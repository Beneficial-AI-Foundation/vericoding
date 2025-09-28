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
ghost fn min_index(a: Seq<i32>, start: nat, end: nat) -> (index: nat)
    requires 0 <= start < end <= a.len()
    ensures start <= index < end,
        forall|i: int| #![trigger a[i]] start <= i < end ==> a[index as int] <= a[i]
{
    if start + 1 == end {
        start
    } else {
        let smaller_end = min_index(a, start + 1, end);
        if a[start as int] <= a[smaller_end as int] {
            start
        } else {
            smaller_end
        }
    }
}

proof fn min_index_ensures(a: Seq<i32>, start: nat, end: nat, i: nat)
    requires 0 <= start < end <= a.len(),
        start <= i < end,
        forall|j: int| #![trigger a[j]] start <= j < end ==> a[i as int] <= a[j]
    ensures forall|k: int| #![trigger a[k]] start <= k < end ==> a[i as int] <= a[k]
{
}

proof fn subrange_to_multiset_after_swap_spec(a: Seq<i32>, i: nat, j: nat)
    requires i < a.len(),
        j < a.len()
    ensures 
        a.update(i as int, a[j as int]).update(j as int, a[i as int]).subrange(0, a.len() as int).to_multiset() ==
        a.subrange(0, a.len() as int).to_multiset()
{
    assert(a.update(i, a[j]).update(j, a[i]).to_multiset() =~= a.to_multiset());
}

proof fn ordered_after_swap_spec(a: Seq<i32>, left: nat, right: nat, i: nat, j: nat)
    requires left <= right <= a.len(),
        left <= i < right,
        left <= j < right,
        i != j,
        forall|k: int| #![trigger a[k]] left < k < right ==> a[k-1] <= a[k],
        if i < j { a[i as int] <= a[j as int] } else { a[j as int] <= a[i as int] }
    ensures ordered(
        a.update(i as int, a[j as int]).update(j as int, a[i as int]),
        left, right
    )
{
    let b = a.update(i as int, a[j as int]).update(j as int, a[i as int]);
    assert(forall|k: int| left < k < right ==> {
        if k == i + 1 {
            if j != i + 1 {
                a[i as int] <= b[i as int] && b[i as int] <= b[k as int]
            } else {
                b[i as int] <= b[k as int]
            }
        } else if k == j + 1 {
            if i != j + 1 {
                a[j as int] <= b[j as int] && b[j as int] <= b[k as int]
            } else {
                b[j as int] <= b[k as int]
            }
        } else if k != i && k != j && k-1 != i && k-1 != j {
            a[k-1] <= a[k]
        } else if k == j && i == j - 1 {
            true
        } else if k == i && j == i - 1 {
            true
        } else {
            true
        }
    });
}

proof fn swap_preserves_preserved(a_old: Seq<i32>, a_new: Seq<i32>, left: nat, right: nat, i: nat, j: nat)
    requires left <= right <= a_old.len(),
        a_old.len() == a_new.len(),
        left <= i < right,
        left <= j < right,
        i != j,
        a_new =~= a_old.update(i as int, a_old[j as int]).update(j as int, a_old[i as int]),
        preserved(a_old, a_new.excl(i as int).excl(j as int), left, right)
    ensures preserved(a_old, a_new, left, right)
{
    assert(a_old.subrange(left as int, right as int).to_multiset() =~= 
           a_old.update(i, a_old[j]).update(j, a_old[i]).subrange(left as int, right as int).to_multiset());
}

proof fn ordered_min_at_position(a: Seq<i32>, left: nat, right: nat, min_pos: nat)
    requires left <= right <= a.len(),
        left <= min_pos < right,
        forall|k: int| #![trigger a[k]] left <= k < right ==> a[min_pos as int] <= a[k]
    ensures forall|k: int| #![trigger a[k]] left < k <= min_pos ==> a[k-1] <= a[k]
{
    assert(forall|k: int| left < k <= min_pos ==> a[k-1] <= a[k]);
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures sorted(old(a)@, a@)
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    if n == 0 {
        return;
    }
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            preserved(old(a)@, a@, 0, n as nat),
            ordered(a@, 0, i as nat)
    {
        let mut min_j = i;
        let mut j = i + 1;
        while j < n
            invariant
                i <= j <= n,
                i <= min_j < n,
                forall|k: int| #![trigger a@[k]] i <= k < j ==> a@[min_j as int] <= a@[k]
        {
            if a[j] < a[min_j] {
                min_j = j;
            }
            j = j + 1;
        }
        
        if min_j != i {
            let old_a = a@;
            a.swap(i, min_j);
            
            proof {
                subrange_to_multiset_after_swap_spec(old_a, i as nat, min_j as nat);
                swap_preserves_preserved(old(a)@, a@, 0, n as nat, i as nat, min_j as nat);
            }
        }
        
        proof {
            if i < n {
                let min_val = a@[i as int];
                assert(forall|k: int| #![trigger a@[k]] i <= k < n ==> min_val <= a@[k]);
                
                if i > 0 {
                    assert(a@[i as int - 1] <= a@[i as int]);
                }
                
                assert(ordered(a@, 0, (i + 1) as nat));
            }
        }
        
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}