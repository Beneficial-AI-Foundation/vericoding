use vstd::prelude::*;

verus! {
    // Ghost function to count even numbers in sequence up to index hi
    spec fn count(hi: nat, s: Seq<int>) -> int
        decreases hi
    {
        if hi == 0 {
            0
        } else if s[hi - 1] % 2 == 0 {
            1 + count((hi - 1) as nat, s)
        } else {
            count((hi - 1) as nat, s)
        }
    }

    // Method to compute count with memoization in array b
    fn foo_count(count_index: usize, a: Seq<int>, b: &mut Vec<i32>) -> (p: usize)
        requires count_index <= a.len()
    {
        if count_index == 0 {
            return 0;
        }
        
        /* code modified by LLM (iteration 1): fixed sequence indexing using proper [] syntax */
        let mut result: usize = 0;
        for i in 0..count_index
            invariant 
                i <= count_index,
                count_index <= a.len()
        {
            if a[i as int] % 2 == 0 {
                result += 1;
            }
        }
        
        if count_index <= b.len() {
            b.set(count_index - 1, result as i32);
        }
        
        result
    }

    // Precompute all count values
    fn foo_precompute(a: Vec<i32>, b: &mut Vec<i32>)
        requires a.len() <= b.len()
    {
        let len = a.len();
        for i in 0..len
            invariant i <= len, len == a.len(), a.len() <= b.len()
        {
            let mut count_even = 0;
            /* code modified by LLM (iteration 1): fixed vector indexing using proper @ syntax */
            for j in 0..(i + 1)
                invariant 
                    j <= i + 1,
                    i < a.len(),
                    a.len() <= b.len()
            {
                if a[j as int] % 2 == 0 {
                    count_even += 1;
                }
            }
            if i < b.len() {
                b.set(i, count_even);
            }
        }
    }

    // Simplified compute count method
    fn compute_count(count_index: usize, a: Seq<int>, b: &mut Vec<i32>) -> (p: usize)
        requires count_index <= a.len()
    {
        /* code modified by LLM (iteration 1): fixed sequence indexing using proper [] syntax */
        let mut result: usize = 0;
        for i in 0..count_index
            invariant 
                i <= count_index,
                count_index <= a.len()
        {
            if a[i as int] % 2 == 0 {
                result += 1;
            }
        }
        result
    }

    // Precompute wrapper
    fn precompute(a: Vec<i32>, b: &mut Vec<i32>) -> (p: usize)
        requires a.len() <= b.len()
    {
        let len = a.len();
        for i in 0..len
            invariant i <= len, len == a.len(), a.len() <= b.len()
        {
            let mut count_even = 0;
            /* code modified by LLM (iteration 1): fixed vector indexing using proper @ syntax */
            for j in 0..(i + 1)
                invariant 
                    j <= i + 1,
                    i < a.len(),
                    a.len() <= b.len()
            {
                if a[j as int] % 2 == 0 {
                    count_even += 1;
                }
            }
            if i < b.len() {
                b.set(i, count_even);
            }
        }
        len
    }

    // Main evens method - simplified version
    fn evens(a: Vec<i32>) -> Vec<Vec<i32>> {
        let mut result = Vec::new();
        /* code modified by LLM (iteration 1): fixed vector indexing using proper [] syntax */
        for i in 0..a.len()
            invariant i <= a.len()
        {
            if a[i as int] % 2 == 0 {
                let mut even_subvec = Vec::new();
                even_subvec.push(a[i as int]);
                result.push(even_subvec);
            }
        }
        result
    }

    // Multiplication method
    fn mult(x: i32, y: i32) -> (r: i32) {
        x * y
    }
}

fn main() {}