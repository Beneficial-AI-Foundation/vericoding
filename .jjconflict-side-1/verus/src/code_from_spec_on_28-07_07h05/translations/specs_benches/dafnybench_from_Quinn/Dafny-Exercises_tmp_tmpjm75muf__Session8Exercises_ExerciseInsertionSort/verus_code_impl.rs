use vstd::prelude::*;

verus! {
    spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
        recommends 0 <= i <= j + 1 <= a.len()
    {
        /* code modified by LLM (iteration 2): Fixed implication operator from 'implies' to '==>' */
        forall|l: int, k: int| i <= l <= k <= j ==> a[l] <= a[k]
    }

    //IMPL insertion_sort
    fn insertion_sort(a: &mut Vec<int>)
        requires old(a).len() > 0,
        ensures 
            sorted_seg(a@, 0, a.len() as int - 1),
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        let mut i = 1;
        while i < a.len()
            invariant
                1 <= i <= a.len(),
                sorted_seg(a@, 0, i as int - 1),
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            let key = a[i];
            let mut j = i;
            
            while j > 0 && a[j - 1] > key
                invariant
                    0 <= j <= i < a.len(),
                    a[i as int] == key,
                    sorted_seg(a@, 0, j as int - 1),
                    sorted_seg(a@, j as int + 1, i as int),
                    /* code modified by LLM (iteration 2): Fixed forall syntax by separating conditions properly */
                    forall|k: int| (j as int < k && k <= i as int) ==> a[k] > key,
                    /* code modified by LLM (iteration 2): Fixed forall syntax by separating conditions properly */
                    forall|k: int| (0 <= k && k < j as int) ==> a[k] <= key,
                    a@.to_multiset() == old(a)@.to_multiset(),
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