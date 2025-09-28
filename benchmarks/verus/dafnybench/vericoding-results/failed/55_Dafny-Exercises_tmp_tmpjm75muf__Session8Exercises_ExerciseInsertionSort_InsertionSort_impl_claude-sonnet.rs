use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: &Vec<i32>, i: int, j: int) -> bool
    recommends 0 <= i <= j + 1 <= a.len()
{
    forall|l: int, k: int| i <= l <= k <= j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn sorted_seg_smaller(a: &Vec<i32>, i: int, j: int) -> bool
    recommends 0 <= i <= j + 1 <= a.len()
{
    forall|l: int, k: int| i <= l < k <= j ==> a[l] <= a[k]
}

proof fn sorted_seg_extend(a: &Vec<i32>, i: int, j: int)
    requires 
        0 <= i <= j + 1 < a.len(),
        sorted_seg(a, i, j),
        forall|k: int| i <= k <= j ==> a[k] <= a[j + 1]
    ensures sorted_seg(a, i, j + 1)
{
    assert forall|l: int, k: int| i <= l <= k <= j + 1 implies a[l] <= a[k] by {
        if k <= j {
            assert(a[l] <= a[k]);
        } else {
            assert(k == j + 1);
            if l <= j {
                assert(a[l] <= a[j + 1]);
            } else {
                assert(l == j + 1);
                assert(a[l] <= a[k]);
            }
        }
    }
}

proof fn multiset_swap_preserves(a: &mut Vec<i32>, i: usize, j: usize, old_a: Vec<i32>)
    requires 
        i < old_a.len(),
        j < old_a.len(),
        old_a.len() == a.len(),
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> old_a[k] == a[k],
        old_a[i as int] == a[j as int],
        old_a[j as int] == a[i as int]
    ensures a@.to_multiset() == old_a@.to_multiset()
{
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(a: &mut Vec<i32>)
    ensures 
        sorted_seg(a, 0, (a.len() - 1) as int),
        a@.to_multiset() == old(a)@.to_multiset(), //Add and prove this
// </vc-spec>
// <vc-code>
{
    let ghost old_a = a@;
    let n = a.len();
    if n <= 1 {
        return;
    }
    
    let mut i = 1;
    while i < n
        invariant
            1 <= i <= n,
            sorted_seg(a, 0, (i - 1) as int),
            a@.to_multiset() == old_a.to_multiset(),
    {
        let key = a[i];
        let mut j = i;
        
        while j > 0 && a[j - 1] > key
            invariant
                0 <= j <= i < n,
                a[i as int] == key,
                forall|k: int| 0 <= k < j ==> a[k] <= key,
                forall|k: int| j < k <= i ==> a[k] > key,
                forall|k: int| (i + 1) <= k < n ==> a[k] == old_a[k],
                sorted_seg(a, 0, (j - 1) as int),
                sorted_seg(a, j + 1, (i - 1) as int),
                a@.to_multiset() == old_a.to_multiset(),
        {
            a.swap(j, j - 1);
            j -= 1;
        }
        
        assert(j == 0 || a[j - 1] <= key);
        assert(forall|k: int| j < k <= i ==> a[k] > key);
        assert(a[j as int] == key);
        
        proof {
            assert forall|l: int, k: int| 0 <= l <= k <= i implies a[l] <= a[k] by {
                if k < j {
                    assert(sorted_seg(a, 0, (j - 1) as int));
                } else if l > j {
                    assert(sorted_seg(a, j + 1, (i - 1) as int));
                } else if l < j && k > j {
                    assert(a[l] <= a[j - 1]);
                    assert(a[j - 1] <= key);
                    assert(a[j as int] == key);
                    assert(a[j as int] <= a[k]);
                } else if l < j && k == j {
                    assert(a[l] <= a[j - 1]);
                    assert(a[j - 1] <= key);
                    assert(a[j as int] == key);
                } else if l == j && k > j {
                    assert(a[j as int] == key);
                    assert(a[j as int] <= a[k]);
                } else {
                    assert(l == j && k == j);
                }
            }
        }
        
        i += 1;
    }
}
// </vc-code>

fn main() {}

}