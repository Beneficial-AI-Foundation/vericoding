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
        let mut i = 1;
        while i < a.len()
            invariant 
                a.len() > 0,
                1 <= i <= a.len(),
                sorted_seg(a@, 0, i as int - 1),
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            let key = a[i];
            let mut j = i;
            
            while j > 0 && a[j - 1] > key
                invariant 
                    0 <= j <= i < a.len(),
                    a@.to_multiset() == old(a)@.to_multiset(),
                    /* code modified by LLM (iteration 1): fixed type mismatch by using sequence indexing */
                    a@[j as int] == key,
                    sorted_seg(a@, 0, j as int - 1),
                    sorted_seg(a@, j as int + 1, i as int),
                    /* code modified by LLM (iteration 1): fixed type mismatches in forall clauses by using sequence indexing */
                    forall|k: int| 0 <= k < j ==> a@[k] <= key,
                    forall|k: int| j < k <= i ==> a@[k] >= key,
            {
                a.set(j, a[j - 1]);
                j -= 1;
            }
            
            a.set(j, key);
            i += 1;
        }
    }
}

fn main() {}