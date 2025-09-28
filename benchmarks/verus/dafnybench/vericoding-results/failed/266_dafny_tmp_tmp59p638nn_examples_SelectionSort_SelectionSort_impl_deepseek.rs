use vstd::prelude::*;

verus! {

spec fn ordered(a: Seq<int>, left: int, right: int) -> bool {
    &&& 0 <= left <= right <= a.len()
    &&& forall |i: int| #![trigger a[i]] left < i < right ==> a[i-1] <= a[i]
}

// <vc-helpers>
spec fn find_min_index(a: Seq<int>, start: int, end: int) -> int
    recommends
        start >= 0,
        end <= a.len(),
        start < end,
    decreases end - start,
{
    if start + 1 == end {
        start
    } else {
        let next_min = find_min_index(a, start + 1, end);
        if a[start] <= a[next_min] {
            start
        } else {
            next_min
        }
    }
}

proof fn find_min_index_ordered_lemma(a: Seq<int>, start: int, end: int)
    requires
        start >= 0,
        end <= a.len(),
        start < end,
    ensures
        find_min_index(a, start, end) >= start,
        find_min_index(a, start, end) < end,
        forall |k: int| start <= k < end ==> a[find_min_index(a, start, end)] <= a[k],
    decreases end - start,
{
    if start + 1 < end {
        find_min_index_ordered_lemma(a, start + 1, end);
    }
}

proof fn swap_preserves_multiset(a: Seq<int>, i: int, j: int) 
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
    ensures
        a.update(i, a[j]).update(j, a[i]).to_multiset() =~= a.to_multiset(),
{
}

proof fn ordered_subrange_lemma(a: Seq<int>, left: int, right: int, i: int)
    requires
        ordered(a, left, right),
        i >= left,
        i < right,
    ensures
        ordered(a, left, i+1),
{
}

proof fn swap_lemma(a: Seq<int>, i: int, j: int, left: int, right: int)
    requires
        0 <= left <= right <= a.len(),
        i >= left, 
        i < right,
        j >= left,
        j < right,
        ordered(a, left, right),
    ensures
        ordered(a.update(i, a[j]).update(j, a[i]), left, i+1),
        a.update(i, a[j]).update(j, a[i]).subrange(left, i+1).to_multiset() =~= a.subrange(left, i+1).to_multiset(),
{
}

proof fn selection_sort_loop_invariant(
    a: Seq<int>, 
    old_a: Seq<int>,
    i: int, 
    n: int
) -> bool 
{
    &&& i >= 0
    &&& i <= n
    &&& n == old_a.len()
    &&& a.len() == old_a.len()
    &&& a.to_multiset() =~= old_a.to_multiset()
    &&& ordered(a, 0, i)
    &&& forall |k: int, l: int| 0 <= k < i <= l < n ==> a[k] <= a[l]
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<int>)
    ensures 
        ordered(a@, 0, a.len() as int),
        a.len() == old(a).len(),
        a@.to_multiset() =~= old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            a.len() == old(a).len(),
            a@.to_multiset() =~= old(a)@.to_multiset(),
            ordered(a@, 0, i as int),
            forall |k: int, l: int| 0 <= k < (i as int) <= l < (n as int) ==> a@[k] <= a@[l],
        decreases n - i,
    {
        let start = i;
        let end = n;
        proof {
            find_min_index_ordered_lemma(a@, start as int, end as int);
        }
        let ghost min_index = find_min_index(a@, start as int, end as int);
        
        if min_index != i as int {
            let temp = a[i];
            a[i] = a[min_index as usize];
            a[min_index as usize] = temp;
            
            proof {
                swap_preserves_multiset(old(a)@, i as int, min_index);
            }
        }
        
        proof {
            let current_a = a@;
            assert(forall |l: int| (i as int) <= l < (n as int) ==> current_a[i as int] <= current_a[l]);
            assert(ordered(current_a, 0, (i as int) + 1));
        }
        
        i += 1;
    }
}
// </vc-code>

fn main() {}

}