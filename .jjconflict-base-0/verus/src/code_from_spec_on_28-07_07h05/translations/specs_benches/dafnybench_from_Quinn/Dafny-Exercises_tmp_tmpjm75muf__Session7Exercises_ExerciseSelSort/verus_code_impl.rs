use vstd::prelude::*;

verus! {
    // Predicate to check if a segment of array is sorted
    spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool 
        recommends 0 <= i <= j <= a.len()
    {
        forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
    }

    //IMPL sel_sort
    fn sel_sort(a: &mut Vec<int>, c: usize, f: usize)
        requires 
            c <= f,
            f <= old(a).len(),
        ensures 
            a.len() == old(a).len(),
            sorted_seg(a@, c as int, f as int),
    {
        let mut i = c;
        while i < f
            invariant
                c <= i <= f,
                f <= a.len(),
                a.len() == old(a).len(),
                sorted_seg(a@, c as int, i as int),
                forall|k: int, l: int| c <= k < i && i <= l < f ==> a[k] <= a[l],
            decreases f - i
        {
            let mut min_idx = i;
            let mut j = i + 1;
            
            while j < f
                invariant
                    i < j <= f,
                    i <= min_idx < j,
                    /* code modified by LLM (iteration 1): added bounds check to ensure array access is safe */
                    min_idx < a.len(),
                    j <= a.len(),
                    /* code modified by LLM (iteration 1): strengthened invariant with proper bounds */
                    forall|k: int| i as int <= k < j as int && k < a.len() as int ==> a[min_idx as int] <= a[k],
                    a.len() == old(a).len(),
                decreases f - j
            {
                /* code modified by LLM (iteration 1): added explicit bounds check before array access */
                assert(j < a.len());
                assert(min_idx < a.len());
                if a[j] < a[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }
            
            if min_idx != i {
                /* code modified by LLM (iteration 1): added bounds assertions before array access */
                assert(i < a.len());
                assert(min_idx < a.len());
                let temp_i = a[i];
                let temp_min = a[min_idx];
                a.set(i, temp_min);
                a.set(min_idx, temp_min_idx);
            }
            
            i += 1;
        }
    }
}

fn main() {}