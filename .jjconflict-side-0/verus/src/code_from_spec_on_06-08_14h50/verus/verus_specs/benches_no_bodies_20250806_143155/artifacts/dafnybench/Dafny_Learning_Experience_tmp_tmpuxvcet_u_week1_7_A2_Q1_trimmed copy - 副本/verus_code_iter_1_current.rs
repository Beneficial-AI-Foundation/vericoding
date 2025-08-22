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
    fn foo_count(count_index: usize, a: Seq<int>, b: &mut Vec<i32>) -> (p: usize) {
        if count_index == 0 {
            return 0;
        }
        
        let mut result = 0;
        for i in 0..count_index {
            if a[i as int] % 2 == 0 {
                result += 1;
            }
        }
        
        if count_index <= b.len() {
            b.set(count_index - 1, result);
        }
        
        result
    }

    // Precompute all count values
    fn foo_precompute(a: Vec<i32>, b: &mut Vec<i32>) {
        let len = a.len();
        for i in 0..len {
            let mut count_even = 0;
            for j in 0..=i {
                if a[j] % 2 == 0 {
                    count_even += 1;
                }
            }
            if i < b.len() {
                b.set(i, count_even);
            }
        }
    }

    // Simplified compute count method
    fn compute_count(count_index: usize, a: Seq<int>, b: &mut Vec<i32>) -> (p: usize) {
        let mut result = 0;
        for i in 0..count_index {
            if a[i as int] % 2 == 0 {
                result += 1;
            }
        }
        result
    }

    // Precompute wrapper
    fn precompute(a: Vec<i32>, b: &mut Vec<i32>) -> (p: usize) {
        let len = a.len();
        for i in 0..len {
            let mut count_even = 0;
            for j in 0..=i {
                if a[j] % 2 == 0 {
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
        for i in 0..a.len() {
            if a[i] % 2 == 0 {
                let mut even_subvec = Vec::new();
                even_subvec.push(a[i]);
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