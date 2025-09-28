use vstd::prelude::*;

verus! {

spec fn ordered(a: Seq<int>, left: int, right: int) -> bool {
    &&& 0 <= left <= right <= a.len()
    &&& forall |i: int| #![trigger a[i]] left < i < right ==> a[i-1] <= a[i]
}

// <vc-helpers>
spec fn min_index_spec(a: Seq<int>, start: int) -> int
    recommends 0 <= start < a.len()
{
    let mut min_idx = start;
    let mut i = start + 1;
    while i < a.len()
        invariant 
            start <= min_idx < a.len(),
            start <= i <= a.len(),
            forall |j: int| #![trigger a[j]] start <= j < i ==> a[min_idx] <= a[j]
        decreases a.len() - i
    {
        if a[i] < a[min_idx] {
            min_idx = i;
        }
        i = i + 1;
    }
    min_idx
}

fn find_min_index(a: &Vec<int>, start: usize) -> (result: usize)
    requires 
        start < a.len(),
    ensures 
        start <= result < a.len(),
        forall |j: int| #![trigger a@[j]] start <= j < a.len() ==> a@[result as int] <= a@[j],
{
    let mut min_idx = start;
    let mut i = start + 1;
    while i < a.len()
        invariant 
            start <= min_idx < a.len(),
            start <= i <= a.len(),
            forall |j: int| #![trigger a@[j]] start <= j < i ==> a@[min_idx as int] <= a@[j]
        decreases a.len() - i
    {
        if a[i] < a[min_idx] {
            min_idx = i;
        }
        i = i + 1;
    }
    min_idx
}

fn swap_elements(a: &mut Vec<int>, i: usize, j: usize)
    requires
        i < old(a).len(),
        j < old(a).len(),
    ensures
        a.len() == old(a).len(),
        a@[i as int] == old(a)@[j as int],
        a@[j as int] == old(a)@[i as int],
        forall |k: int| #![trigger a@[k]] 0 <= k < a.len() && k != i && k != j ==> a@[k] == old(a)@[k],
        a@.to_multiset() =~= old(a)@.to_multiset(),
{
    if i != j {
        let temp = a[i];
        a.set(i, a[j]);
        a.set(j, temp);
    }
}

proof fn ordered_prefix_preserved(a: Seq<int>, b: Seq<int>, left: int, right: int, swap_pos: int)
    requires
        a.len() == b.len(),
        0 <= left <= right <= a.len(),
        left <= swap_pos < right,
        ordered(a, left, swap_pos + 1),
        forall |i: int| swap_pos < i < a.len() ==> b[swap_pos] <= a[i],
        forall |i: int| #![trigger a[i], b[i]] 0 <= i < a.len() && i != swap_pos ==> a[i] == b[i],
        b[swap_pos] <= a[swap_pos]
    ensures
        ordered(b, left, swap_pos + 1)
{
}

proof fn ordered_step_lemma(a: Seq<int>, left: int, right: int)
    requires
        0 <= left < right <= a.len(),
        ordered(a, left, right),
        forall |i: int| #![trigger a[i]] right <= i < a.len() ==> a[right-1] <= a[i]
    ensures
        ordered(a, left, right + 1)
{
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
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= old(a).len(),
            a.len() == old(a).len(),
            ordered(a@, 0, i as int),
            a@.to_multiset() =~= old(a)@.to_multiset(),
            forall |j: int, k: int| #![trigger a@[j], a@[k]] 0 <= j < i && i <= k < a.len() ==> a@[j] <= a@[k]
        decreases old(a).len() - i
    {
        if i < a.len() {
            let min_idx = find_min_index(a, i);
            
            assert(forall |j: int| #![trigger a@[j]] i <= j < a.len() ==> a@[min_idx as int] <= a@[j]);
            
            if min_idx != i {
                let old_a = a@;
                swap_elements(a, i, min_idx);
                
                assert(a@.to_multiset() =~= old(a)@.to_multiset());
                
                proof {
                    ordered_prefix_preserved(old_a, a@, 0, a.len() as int, i as int);
                }
            }
            
            assert(forall |j: int| #![trigger a@[j]] (i as int) + 1 <= j < a.len() ==> a@[i as int] <= a@[j]);
            
            proof {
                if i > 0 {
                    ordered_step_lemma(a@, 0, (i as int) + 1);
                }
            }
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}