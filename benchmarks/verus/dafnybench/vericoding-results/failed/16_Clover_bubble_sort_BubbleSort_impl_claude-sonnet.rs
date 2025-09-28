use vstd::prelude::*;

verus! {

// <vc-helpers>
fn is_sorted(a: &Vec<i32>) -> (result: bool)
    requires a.len() > 0
    ensures result <==> (forall|i: int, j: int| 0 <= i < j < a.len() ==> #[trigger] a[i] <= #[trigger] a[j])
{
    if a.len() <= 1 {
        return true;
    }
    
    let mut i = 0;
    while i < a.len() - 1
        invariant
            0 <= i <= a.len() - 1,
            a.len() > 0,
            forall|k: int, l: int| 0 <= k < l <= i ==> #[trigger] a[k] <= #[trigger] a[l]
        decreases a.len() - 1 - i
    {
        if a[i] > a[i + 1] {
            return false;
        }
        i += 1;
    }
    true
}

proof fn swap_preserves_multiset<T>(v: &Vec<T>, i: usize, j: usize)
    requires 
        i < v.len(),
        j < v.len(),
    ensures
        v@.update(i as int, v@[j as int]).update(j as int, v@[i as int]).to_multiset() == v@.to_multiset()
{
    if i == j {
        assert(v@.update(i as int, v@[j as int]).update(j as int, v@[i as int]) == v@);
    } else {
        let v1 = v@.update(i as int, v@[j as int]);
        let v2 = v1.update(j as int, v@[i as int]);
        vstd::multiset::lemma_multiset_swap(v@, i as int, j as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &mut Vec<i32>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    if n <= 1 {
        return;
    }
    
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == a.len(),
            // Elements 0..i are sorted
            forall|k: int, l: int| 0 <= k < l < i ==> a@[k] <= a@[l],
            // Elements i..n are greater than or equal to all elements in 0..i
            forall|k: int, l: int| 0 <= k < i && i <= l < n ==> a@[k] <= a@[l],
            a@.to_multiset() == old(a)@.to_multiset(),
        decreases n - i
    {
        let mut j = 0;
        let limit = n - 1 - i;
        while j < limit
            invariant
                0 <= j <= limit,
                limit == n - 1 - i,
                0 <= i < n,
                n == a.len(),
                // Previous elements are still sorted
                forall|k: int, l: int| 0 <= k < l < i ==> a@[k] <= a@[l],
                // Elements i..n are still >= elements in 0..i
                forall|k: int, l: int| 0 <= k < i && i <= l < n ==> a@[k] <= a@[l],
                // In current pass, largest element has bubbled to position j
                forall|k: int| 0 <= k <= j ==> a@[k] <= a@[j as int],
                // Multiset preserved
                a@.to_multiset() == old(a)@.to_multiset(),
            decreases limit - j
        {
            assert(j < n - 1 - i);
            assert(j + 1 <= n - 1 - i);
            assert(j + 1 < n);
            
            if a[j] > a[j + 1] {
                proof {
                    swap_preserves_multiset(a, j, j + 1);
                }
                let temp = a[j];
                let next_val = a[j + 1];
                a.set(j, next_val);
                a.set(j + 1, temp);
            }
            j += 1;
        }
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}