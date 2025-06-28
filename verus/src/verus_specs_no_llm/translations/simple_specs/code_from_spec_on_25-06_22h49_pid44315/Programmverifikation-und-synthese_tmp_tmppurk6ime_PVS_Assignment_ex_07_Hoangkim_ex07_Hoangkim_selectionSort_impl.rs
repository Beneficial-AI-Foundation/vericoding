use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindMin(a: &Vec<int>, lo: usize) -> (minIdx: usize)
    requires 
        a.len() > 0,
        lo < a.len()
    ensures 
        lo <= minIdx < a.len(),
        forall|x: int| lo as int <= x < a.len() ==> a[minIdx as int] <= a[x]
{
    let mut minIdx = lo;
    let mut i = lo + 1;
    
    while i < a.len()
        invariant
            lo <= minIdx < a.len(),
            lo + 1 <= i <= a.len(),
            forall|x: int| lo as int <= x < i as int ==> a[minIdx as int] <= a[x]
    {
        if a[i as int] < a[minIdx as int] {
            minIdx = i;
        }
        i = i + 1;
    }
    
    minIdx
}

fn swap(a: &mut Vec<int>, i: usize, j: usize)
    requires 
        old(a).len() > 0,
        i < old(a).len(),
        j < old(a).len()
    ensures
        a.len() == old(a).len(),
        a[i as int] == old(a)[j as int],
        a[j as int] == old(a)[i as int],
        forall|k: int| 0 <= k < a.len() && k != i as int && k != j as int ==> a[k] == old(a)[k]
{
    let temp = a[i as int];
    a.set(i, a[j as int]);
    a.set(j, temp);
}

spec fn is_sorted(a: &Vec<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}

spec fn multiset_eq(a: &Vec<int>, b: &Vec<int>) -> bool {
    a.len() == b.len() &&
    forall|val: int| count_in_vec(a, val) == count_in_vec(b, val)
}

spec fn count_in_vec(a: &Vec<int>, val: int) -> nat {
    count_in_range(a, val, 0, a.len() as int)
}

spec fn count_in_range(a: &Vec<int>, val: int, start: int, end: int) -> nat
    recommends 0 <= start <= end <= a.len()
    decreases end - start
{
    if start >= end {
        0
    } else {
        let count_rest = count_in_range(a, val, start + 1, end);
        if a[start] == val {
            1 + count_rest
        } else {
            count_rest
        }
    }
}

proof fn lemma_swap_multiset(a: &Vec<int>, b: &Vec<int>, i: int, j: int)
    requires
        a.len() == b.len(),
        0 <= i < a.len(),
        0 <= j < a.len(),
        a[i] == b[j],
        a[j] == b[i],
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a[k] == b[k]
    ensures
        multiset_eq(a, b)
{
    assert forall|val: int| count_in_vec(a, val) == count_in_vec(b, val) by {
        lemma_count_swap_helper(a, b, val, i, j, 0, a.len() as int);
    }
}

proof fn lemma_count_swap_helper(a: &Vec<int>, b: &Vec<int>, val: int, i: int, j: int, start: int, end: int)
    requires
        a.len() == b.len(),
        0 <= i < a.len(),
        0 <= j < a.len(),
        a[i] == b[j],
        a[j] == b[i],
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a[k] == b[k],
        0 <= start <= end <= a.len()
    ensures
        count_in_range(a, val, start, end) == count_in_range(b, val, start, end)
    decreases end - start
{
    if start >= end {
        // Base case: empty range
    } else {
        // Recursive case
        lemma_count_swap_helper(a, b, val, i, j, start + 1, end);
        
        // Now we need to show the counts at position `start` are correct
        if start == i {
            // a[i] == b[j], so we need to consider if val == a[i] == b[j]
            // and we know that b[i] == a[j]
        } else if start == j {
            // a[j] == b[i], so we need to consider if val == a[j] == b[i]  
            // and we know that b[j] == a[i]
        } else {
            // a[start] == b[start], so the contribution is the same
            assert(a[start] == b[start]);
        }
    }
}

proof fn lemma_multiset_transitive(a: &Vec<int>, b: &Vec<int>, c: &Vec<int>)
    requires
        multiset_eq(a, b),
        multiset_eq(b, c)
    ensures
        multiset_eq(a, c)
{
    assert(a.len() == c.len());
    assert forall|val: int| count_in_vec(a, val) == count_in_vec(c, val) by {
        assert(count_in_vec(a, val) == count_in_vec(b, val));
        assert(count_in_vec(b, val) == count_in_vec(c, val));
    }
}

proof fn lemma_multiset_refl(a: &Vec<int>)
    ensures multiset_eq(a, a)
{
    assert forall|val: int| count_in_vec(a, val) == count_in_vec(a, val) by {}
}

fn selectionSort(a: &mut Vec<int>)
    requires a.len() > 0
    ensures
        a.len() == old(a).len(),
        is_sorted(a),
        multiset_eq(a, old(a))
{
    let mut i: usize = 0;
    let ghost orig_a = *a;
    let ghost orig_len = a.len();
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == orig_len,
            // Elements before i are sorted
            forall|x: int, y: int| 0 <= x <= y < i as int ==> a[x] <= a[y],
            // Elements before i are no larger than elements from i onwards  
            forall|x: int, y: int| 0 <= x < i as int && i as int <= y < a.len() ==> a[x] <= a[y],
            // Multiset equality is preserved
            multiset_eq(a, &orig_a)
    {
        let ghost old_a = *a;
        let minIdx = FindMin(a, i);
        
        // Swap the minimum element to position i
        swap(a, i, minIdx);
        
        // Prove multiset equality is preserved after swap
        proof {
            lemma_swap_multiset(a, &old_a, i as int, minIdx as int);
            lemma_multiset_transitive(a, &old_a, &orig_a);
        }
        
        // Prove the partitioning property is maintained
        assert(forall|y: int| (i + 1) as int <= y < a.len() ==> a[i as int] <= a[y]) by {
            // The element at position i was the minimum among elements from i to end
            assert(forall|x: int| i as int <= x < old_a.len() ==> old_a[minIdx as int] <= old_a[x]);
            // After swap, a[i] = old_a[minIdx]
            assert(a[i as int] == old_a[minIdx as int]);
            // Elements in range [i+1, end) either stayed the same or one element moved from minIdx
            assert forall|y: int| (i + 1) as int <= y < a.len() implies a[i as int] <= a[y] by {
                if y == minIdx as int {
                    // a[y] = old_a[i], and old_a[minIdx] <= old_a[i] by FindMin postcondition
                    assert(old_a[minIdx as int] <= old_a[i as int]);
                    assert(a[i as int] == old_a[minIdx as int]);
                    assert(a[y] == old_a[i as int]);
                } else {
                    // a[y] = old_a[y], and old_a[minIdx] <= old_a[y] by FindMin postcondition  
                    assert(a[y] == old_a[y]);
                    assert(old_a[minIdx as int] <= old_a[y]);
                    assert(a[i as int] == old_a[minIdx as int]);
                }
            }
        }
        
        i = i + 1;
    }
}

}