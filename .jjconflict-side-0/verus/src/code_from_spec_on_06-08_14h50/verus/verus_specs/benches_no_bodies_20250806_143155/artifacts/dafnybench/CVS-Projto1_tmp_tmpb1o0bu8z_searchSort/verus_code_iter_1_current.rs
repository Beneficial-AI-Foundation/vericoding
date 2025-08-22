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
                count <= c,
        {
            if a[i] == k {
                count = count + 1;
                if count >= c {
                    return true;
                }
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
        
        while i + b.len() <= a.len()
            invariant i <= a.len()
        {
            let mut j: usize = 0;
            let mut found = true;
            
            while j < b.len()
                invariant 
                    j <= b.len(),
                    i + j < a.len() || j == b.len(),
            {
                if i + j >= a.len() || a[i + j] != b[j] {
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