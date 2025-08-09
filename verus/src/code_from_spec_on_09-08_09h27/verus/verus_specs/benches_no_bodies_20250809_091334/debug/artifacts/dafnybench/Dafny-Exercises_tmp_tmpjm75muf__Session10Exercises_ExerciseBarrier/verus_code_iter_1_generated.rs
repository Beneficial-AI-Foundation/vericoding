use vstd::prelude::*;

verus! {
    fn barrier(v: &[int], p: usize) -> (b: bool)
        requires 
            v.len() > 0,
            p < v.len(),
        ensures 
            b == (forall|k: int, l: int| 0 <= k <= p && p < l < v.len() ==> v[k] < v[l])
    {
        if p + 1 >= v.len() {
            return true;
        }
        
        let mut max_left = v[0];
        let mut i = 1;
        while i <= p
            invariant 
                1 <= i <= p + 1,
                max_left == (forall|j: int| 0 <= j < i ==> v[j] <= max_left),
                exists|j: int| 0 <= j < i && v[j] == max_left,
        {
            if v[i] > max_left {
                max_left = v[i];
            }
            i += 1;
        }
        
        let mut min_right = v[p + 1];
        let mut j = p + 2;
        while j < v.len()
            invariant 
                p + 2 <= j <= v.len(),
                min_right == (forall|k: int| p + 1 <= k < j ==> min_right <= v[k]),
                exists|k: int| p + 1 <= k < j && v[k] == min_right,
        {
            if v[j] < min_right {
                min_right = v[j];
            }
            j += 1;
        }
        
        max_left < min_right
    }
}

fn main() {}