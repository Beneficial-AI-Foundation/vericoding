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
        
        while i < n
            invariant 
                i <= n,
                count <= i,
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
        
        while i <= a.len() - b.len()
            invariant i <= a.len() - b.len() + 1,
        {
            let mut j: usize = 0;
            let mut found = true;
            
            while j < b.len()
                invariant 
                    j <= b.len(),
                    i + j <= a.len(),
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