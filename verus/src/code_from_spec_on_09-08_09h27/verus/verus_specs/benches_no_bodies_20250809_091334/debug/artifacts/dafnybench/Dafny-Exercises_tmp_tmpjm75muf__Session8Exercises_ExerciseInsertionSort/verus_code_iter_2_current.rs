use vstd::prelude::*;

verus! {
    spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
        recommends 0 <= i <= j + 1 <= a.len()
    {
        forall|l: int, k: int| i <= l <= k <= j ==> a[l] <= a[k]
    }

    fn insertion_sort(a: &mut Vec<int>)
        requires old(a).len() > 0,
        ensures 
            sorted_seg(a@, 0, a.len() as int - 1),
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        let n = a.len();
        for i in 1..n
            invariant
                a@.to_multiset() == old(a)@.to_multiset(),
                sorted_seg(a@, 0, i as int - 1),
        {
            let key = a[i];
            let mut j = i;
            
            while j > 0 && a[j - 1] > key
                invariant
                    j <= i,
                    a@.to_multiset() == old(a)@.to_multiset(),
                    sorted_seg(a@, 0, j as int - 1),
                    sorted_seg(a@, j as int + 1, i as int),
                    /* code modified by LLM (iteration 1): fixed type mismatches by using sequence access a@[k] consistently instead of mixing direct indexing a[k as usize] */
                    forall|k: int| j < k <= i ==> a@[k] > key,
                    forall|k: int| 0 <= k < j ==> a@[k] <= key,
            {
                a[j] = a[j - 1];
                j -= 1;
            }
            
            a[j] = key;
        }
    }
}

fn main() {}