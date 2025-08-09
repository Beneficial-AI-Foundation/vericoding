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
        
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
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
        
        /* code modified by LLM (iteration 1): added decreases clause and fixed loop bound */
        while i <= a.len() - b.len()
            invariant 
                i <= a.len() - b.len() + 1,
                b.len() > 0,
            decreases a.len() - b.len() + 1 - i
        {
            let mut j: usize = 0;
            let mut found = true;
            
            /* code modified by LLM (iteration 1): added decreases clause for inner loop */
            while j < b.len()
                invariant 
                    j <= b.len(),
                    i + j <= a.len(),
                    i <= a.len() - b.len(),
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