use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn is_sorted_from(s: Seq<i32>, start: int) -> bool {
    forall|i: int, j: int| start <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn prefix_sorted_and_bounded(s: Seq<i32>, k: int) -> bool {
    k == 0 || (
        is_sorted_from(s, 0) && 
        forall|i: int, j: int| 0 <= i < k && k <= j < s.len() ==> s[i] <= s[j]
    )
}

proof fn sorted_trans(s: Seq<i32>, start: int, mid: int)
    requires 
        0 <= start <= mid < s.len(),
        is_sorted_from(s, start),
    ensures
        is_sorted_from(s, mid),
{
}

proof fn prefix_extension(s: Seq<i32>, k: int)
    requires 
        0 <= k < s.len(),
        prefix_sorted_and_bounded(s, k),
    ensures
        prefix_sorted_and_bounded(s, k + 1),
{
}

proof fn swap_preserves_multiset<T>(v1: Seq<T>, v2: Seq<T>, i: int, j: int)
    requires
        0 <= i < v1.len(),
        0 <= j < v1.len(),
        v1.len() == v2.len(),
        v2[i] == v1[j],
        v2[j] == v1[i],
        forall|k: int| 0 <= k < v1.len() && k != i && k != j ==> v1[k] == v2[k],
    ensures
        v1.to_multiset() == v2.to_multiset(),
{
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let ghost old_a_view = a@;
    
    for i in 0..n
        invariant
            a@.to_multiset() == old_a_view.to_multiset(),
            prefix_sorted_and_bounded(a@, i as int),
    {
        let mut min_idx = i;
        
        for j in (i + 1)..n
            invariant
                a@.to_multiset() == old_a_view.to_multiset(),
                prefix_sorted_and_bounded(a@, i as int),
                i <= min_idx < n,
                forall|k: int| i <= k < j ==> #[trigger] a@[min_idx as int] <= a@[k],
        {
            assert(j < n);
            assert(min_idx < n);
            if a[j] < a[min_idx] {
                min_idx = j;
            }
        }
        
        if min_idx != i {
            assert(i < n);
            assert(min_idx < n);
            let temp = a[i];
            let min_val = a[min_idx];
            let ghost old_a_pre_swap = a@;
            a.set(i, min_val);
            a.set(min_idx, temp);
            
            proof {
                swap_preserves_multiset(old_a_pre_swap, a@, i as int, min_idx as int);
            }
        }
        
        proof {
            if (i + 1) < n {
                prefix_extension(a@, i as int);
            }
        }
    }
}
// </vc-code>

fn main() {}

}