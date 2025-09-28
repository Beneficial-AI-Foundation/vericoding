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
spec fn sorted_seq(a: Seq<i32>) -> bool {
    ordered(a, 0, a.len() as nat)
}

proof fn ordered_subrange(a: Seq<i32>, left: nat, mid: nat, right: nat)
    requires
        left <= mid <= right <= a.len(),
        ordered(a, left, right),
    ensures
        ordered(a, left, mid) && ordered(a, mid, right)
{
}

proof fn ordered_combine(a: Seq<i32>, left: nat, mid: nat, right: nat)
    requires
        left <= mid <= right <= a.len(),
        ordered(a, left, mid),
        ordered(a, mid, right),
        (mid > left && mid < right) ==> a[(mid-1) as int] <= a[mid as int],
    ensures
        ordered(a, left, right)
{
}

proof fn preserved_transitive(a: Seq<i32>, b: Seq<i32>, c: Seq<i32>, left: nat, right: nat)
    requires
        a.len() == b.len() == c.len(),
        left <= right <= a.len(),
        preserved(a, b, left, right),
        preserved(b, c, left, right),
    ensures
        preserved(a, c, left, right)
{
}

proof fn preserved_subrange(a: Seq<i32>, b: Seq<i32>, left: nat, mid: nat, right: nat)
    requires
        a.len() == b.len(),
        left <= mid <= right <= a.len(),
        preserved(a, b, left, right),
    ensures
        preserved(a, b, left, mid) && preserved(a, b, mid, right)
{
}

spec fn min_index(a: Seq<i32>, start: nat, end: nat) -> nat
    recommends start < end <= a.len()
{
    choose|min_idx: nat| #![trigger a[min_idx as int], a[start as int]] 
        start <= min_idx < end && 
        forall|j: nat| #![trigger a[j as int]] start <= j < end ==> a[min_idx as int] <= a[j as int]
}

proof fn preserved_swap(a: Seq<i32>, b: Seq<i32>, idx1: nat, idx2: nat, left: nat, right: nat)
    requires
        a.len() == b.len(),
        left <= right <= a.len(),
        left <= idx1 < right,
        left <= idx2 < right,
        b == a.set(idx1 as int, a[idx2 as int]).set(idx2 as int, a[idx1 as int]),
        forall|i: nat| #![trigger a[i as int]] i < left || i >= right ==> a[i as int] == b[i as int],
    ensures
        preserved(a, b, left, right)
{
}

proof fn preserved_refl(a: Seq<i32>, left: nat, right: nat)
    requires
        left <= right <= a.len(),
    ensures
        preserved(a, a, left, right)
{
}

proof fn min_index_property(a: Seq<i32>, start: nat, end: nat)
    requires
        start < end <= a.len(),
    ensures
        let min_idx = min_index(a, start, end);
        start <= min_idx < end,
        forall|j: nat| start <= j < end ==> a[min_idx as int] <= a[j as int]
{
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures sorted(old(a)@, a@)
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let n = a.len();
    
    proof {
        preserved_refl(old(a)@, 0, n as nat);
    }
    
    while i < n
        invariant
            i <= n,
            ordered(a@, 0, i as nat),
            forall|k: nat, l: nat| 0 <= k < i as nat <= l < n as nat ==> a@[k as int] <= a@[l as int],
            preserved(old(a)@, a@, 0, n as nat),
        decreases n - i
    {
        let mut min_idx = i;
        let mut j = i + 1;
        
        proof {
            min_index_property(a@, i as nat, n as nat);
        }
        
        while j < n
            invariant
                i <= j <= n,
                i <= min_idx < n,
                min_idx < j || j == i + 1,
                forall|k: nat| i as nat <= k < j as nat ==> a@[min_idx as int] <= a@[k as int],
            decreases n - j
        {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        
        if min_idx != i {
            let temp = a[i];
            a[i] = a[min_idx];
            a[min_idx] = temp;
            
            proof {
                let old_seq = a@;
                a[min_idx] = temp;
                let new_seq = a@;
                preserved_swap(old_seq, new_seq, i as nat, min_idx as nat, 0, n as nat);
            }
        }
        
        proof {
            if i > 0 {
                assert(a@[i as int - 1] <= a@[i as int]);
            }
        }
        
        i += 1;
    }
    
    proof {
        assert(ordered(a@, 0, n as nat));
        assert(preserved(old(a)@, a@, 0, n as nat));
        assert(sorted(old(a)@, a@));
    }
}
// </vc-code>

fn main() {
}

}