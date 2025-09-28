use vstd::prelude::*;

verus! {

// Works by dividing the input list into two parts: sorted and unsorted. At the beginning, 
// the sorted part is empty and the unsorted part contains all the elements.

// <vc-helpers>
use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::seq::*;

#[verifier(inline)]
spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

#[verifier::inline]
spec fn find_min_index(s: Seq<i32>, start: int) -> int
    recommends
        0 <= start <= s.len(),
    decreases s.len() - start,
{
    if start >= s.len() {
        start
    } else {
        let next = find_min_index(s, start + 1);
        if next < s.len() && s[next] < s[start] {
            next
        } else {
            start
        }
    }
}

proof fn find_min_index_valid(s: Seq<i32>, start: int)
    requires
        0 <= start <= s.len(),
    ensures
        start <= find_min_index(s, start) <= s.len(),
        find_min_index(s, start) == s.len() || (forall|j: int| start <= j < s.len() ==> s[find_min_index(s, start)] <= s[j]),
    decreases s.len() - start,
{
    if start < s.len() {
        find_min_index_valid(s, start + 1);
    }
}

spec fn swap_multiset_equiv(ms: Multiset<i32>, i: int, j: int) -> bool {
    ms == ms
}

proof fn swap_preserves_multiset(s: Seq<i32>, i: int, j: int) 
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.to_multiset() == s.update(i, s[j]).update(j, s[i]).to_multiset(),
{
}

proof fn sorted_subrange_preserves_ordering(s: Seq<i32>, i: int)
    requires
        0 <= i <= s.len(),
        is_sorted(s.subrange(0, i as int)),
        forall|k: int| 0 <= k < i ==> (forall|l: int| i <= l < s.len() ==> s[k] <= s[l]),
    ensures
        is_sorted(s.subrange(0, (i+1) as int)),
{
}

proof fn find_min_implies_forall(s: Seq<i32>, start: int, min_index: int)
    requires
        0 <= start <= s.len(),
        start <= min_index < s.len(),
        forall|k: int| start <= k < s.len() ==> s[min_index] <= s[k],
    ensures
        forall|j: int| start <= j < s.len() ==> s[min_index] <= s[j],
{
}

proof fn assert_is_sorted_subrange(s: Seq<i32>, i: usize)
    requires
        is_sorted(s.subrange(0, i as int)),
    ensures
        is_sorted(s.subrange(0, i)),
{
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures
        // Ensures the final array is sorted in ascending order
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        // Ensures that the final array has the same elements as the initial array
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let ghost n: int = a@.len();
    
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            is_sorted(a@.subrange(0, i as int)),
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|k: int| 0 <= k < i ==> (forall|l: int| i <= l < a@.len() ==> a@[k] <= a@[l]),
        decreases n - i as int,
    {
        let mut min_index = i;
        let mut j: usize = i + 1;
        
        assert(i < a.len());
        
        while j < a.len()
            invariant
                i <= min_index < a.len(),
                i <= j <= a@.len(),
                forall|k: int| i <= k < j as int ==> a@[min_index as int] <= a@[k],
            decreases a.len() - j,
        {
            if a[j] < a[min_index] {
                min_index = j;
            }
            j += 1;
        }
        
        assert(a@.to_multiset() == old(a)@.to_multiset());
        
        if min_index != i {
            let temp = a[i];
            a[i] = a[min_index];
            a[min_index] = temp;
            
            proof {
                swap_preserves_multiset(a@, i as int, min_index as int);
            }
        }
        
        proof {
            find_min_implies_forall(a@, i as int, min_index as int);
            assert(forall|k: int| i as int <= k < a@.len() ==> a@[i as int] <= a@[k]);
            sorted_subrange_preserves_ordering(a@, i as int);
        }
        
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}