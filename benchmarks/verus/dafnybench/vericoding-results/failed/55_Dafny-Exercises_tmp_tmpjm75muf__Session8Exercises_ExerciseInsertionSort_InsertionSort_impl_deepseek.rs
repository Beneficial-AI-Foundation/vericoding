use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: &Vec<i32>, i: int, j: int) -> bool
    recommends 0 <= i <= j + 1 <= a.len()
{
    forall|l: int, k: int| i <= l <= k <= j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn sorted_seg_seq(s: Seq<i32>, i: int, j: int) -> bool
    recommends 0 <= i <= j + 1 <= s.len()
{
    forall|l: int, k: int| i <= l <= k <= j ==> s[l] <= s[k]
}

proof fn sorted_seg_seq_equiv(a: &Vec<i32>, i: int, j: int)
    requires 0 <= i <= j + 1 <= a.len()
    ensures sorted_seg(a, i, j) == sorted_seg_seq(a@, i, j)
{
}

proof fn sorted_seg_empty(a: &Vec<i32>, i: int)
    requires 0 <= i <= a.len()
    ensures sorted_seg(a, i, i - 1)
{
}

proof fn sorted_seg_extend(a: &Vec<i32>, i: int, j: int, k: int)
    requires 
        0 <= i <= j <= k < a.len(),
        sorted_seg(a, i, j),
        sorted_seg(a, j + 1, k),
        a[j] <= a[j + 1]
    ensures sorted_seg(a, i, k)
{
}

proof fn sorted_seg_insert(a: &Vec<i32>, pos: int, value: i32, i: int, j: int)
    requires
        0 <= i <= pos <= j < a.len(),
        sorted_seg(a, i, j),
        (i == pos || a[pos - 1] <= value),
        (pos == j || value <= a[pos + 1])
    ensures sorted_seg_seq(a@.update(pos, value), i, j)
{
}

proof fn multiset_update_eq<T>(s: Seq<T>, i: int, x: T, y: T)
    requires 0 <= i < s.len(), x == y
    ensures s.update(i, x).to_multiset() == s.to_multiset()
{
}

proof fn multiset_update_swap<T>(s: Seq<T>, i: int, j: int, x: T, y: T)
    requires 0 <= i < j < s.len()
    ensures s.update(i, x).update(j, y).to_multiset() == s.update(j, y).update(i, x).to_multiset()
{
}

proof fn multiset_update_shift<T>(s: Seq<T>, i: int, x: T, y: T)
    requires 0 <= i < s.len() - 1
    ensures s.update(i, x).update(i + 1, y).to_multiset() == s.update(i + 1, y).update(i, x).to_multiset()
{
    multiset_update_swap(s, i, i + 1, x, y);
}

proof fn multiset_update_shift_usize<T>(s: Seq<T>, i: usize, x: T, y: T)
    requires 0 <= i < s.len() - 1
    ensures s.update(i as int, x).update(i as int + 1, y).to_multiset() == s.update(i as int + 1, y).update(i as int, x).to_multiset()
{
    multiset_update_swap(s, i as int, i as int + 1, x, y);
}

proof fn multiset_update_eq_usize<T>(s: Seq<T>, i: usize, x: T, y: T)
    requires 0 <= i < s.len(), x == y
    ensures s.update(i as int, x).to_multiset() == s.to_multiset()
{
    multiset_update_eq(s, i as int, x, y);
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
    let mut i: usize = 1;
    while i < a.len()
        invariant 
            0 < i <= a.len(),
            sorted_seg(a, 0, (i - 1) as int),
            a@.to_multiset() == old(a)@.to_multiset()
        decreases a.len() - i
    {
        let key = a[i];
        let mut j: usize = i;
        
        proof {
            sorted_seg_seq_equiv(a, 0, (i - 1) as int);
        }
        
        while j > 0 && a[j - 1] > key
            invariant 
                0 <= j <= i,
                j <= i <= a.len(),
                sorted_seg(a, 0, (i - 1) as int),
                forall|k: int| j <= k < i ==> a[k] > key,
                a@.to_multiset() == old(a)@.to_multiset()
            decreases j
        {
            assert(j > 0);
            a[j] = a[j - 1];
            j = j - 1;
            
            proof {
                multiset_update_shift_usize(a@, j, a[j + 1], a[j]);
            }
        }
        
        a[j] = key;
        
        proof {
            if j < i {
                sorted_seg_insert(a, j as int, key, 0, (i - 1) as int);
            }
            multiset_update_eq_usize(a@, j, a[j], key);
        }
        
        i = i + 1;
    }
    
    proof {
        if a.len() > 0 {
            sorted_seg_seq_equiv(a, 0, (a.len() - 1) as int);
        } else {
            sorted_seg_empty(a, 0);
        }
    }
}
// </vc-code>

fn main() {}

}