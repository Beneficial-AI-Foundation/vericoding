use vstd::prelude::*;

verus! {
    fn fillK(a: &[int], n: usize, k: int, c: usize) -> (b: bool)
        requires 
            c <= n,
            n == a.len(),
        ensures true,
    {
        let mut count: usize = 0;
        let mut i: usize = 0;
        
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        while i < n
            invariant 
                i <= n,
                count <= i,
            decreases n - i
        {
            if a[i] == k {
                count = count + 1;
            }
            i = i + 1;
        }
        
        count >= c
    }

    fn containsSubString(a: &[char], b: &[char]) -> (pos: isize)
        requires 
            b.len() <= a.len(),
        ensures true,
    {
        if b.len() == 0 {
            return 0;
        }
        
        let mut i: usize = 0;
        
        /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
        while i <= a.len() - b.len()
            invariant i <= a.len() - b.len() + 1
            decreases a.len() - b.len() + 1 - i
        {
            let mut j: usize = 0;
            let mut found = true;
            
            /* code modified by LLM (iteration 2): added decreases clause to inner loop */
            while j < b.len()
                invariant 
                    j <= b.len(),
                    /* code modified by LLM (iteration 1): fixed type mismatch by using int for loop variable k to match comparison operators */
                    found ==> (forall|k: int| 0 <= k < j ==> a[i + k] == b[k])
                decreases b.len() - j
            {
                if a[i + j] != b[j] {
                    found = false;
                    break;
                }
                j = j + 1;
            }
            
            if found {
                return i as isize;
            }
            
            i = i + 1;
        }
        
        -1
    }
}

fn main() {}