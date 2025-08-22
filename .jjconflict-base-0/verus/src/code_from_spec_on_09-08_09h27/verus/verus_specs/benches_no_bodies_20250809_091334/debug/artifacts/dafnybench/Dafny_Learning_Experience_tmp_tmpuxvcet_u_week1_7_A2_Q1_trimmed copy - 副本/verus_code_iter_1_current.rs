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
            0
        } else {
            let mut even_count = 0;
            let mut i = 0;
            while i < count_index {
                if a[i] % 2 == 0 {
                    even_count += 1;
                }
                i += 1;
            }
            even_count
        }
    }

    // Precompute all count values
    fn foo_precompute(a: Vec<i32>, b: &mut Vec<i32>) {
        let len = a.len();
        b.truncate(0);
        let mut i = 0;
        while i <= len {
            let mut even_count = 0;
            let mut j = 0;
            while j < i {
                if a[j] % 2 == 0 {
                    even_count += 1;
                }
                j += 1;
            }
            b.push(even_count);
            i += 1;
        }
    }

    // Simplified compute count method
    fn compute_count(count_index: usize, a: Seq<int>, b: &mut Vec<i32>) -> (p: usize) {
        let mut even_count = 0;
        let mut i = 0;
        while i < count_index {
            if a[i] % 2 == 0 {
                even_count += 1;
            }
            i += 1;
        }
        even_count
    }

    // Precompute wrapper
    fn precompute(a: Vec<i32>, b: &mut Vec<i32>) -> (p: usize) {
        let len = a.len();
        b.truncate(0);
        let mut i = 0;
        while i <= len {
            let mut even_count = 0;
            let mut j = 0;
            while j < i {
                if a[j] % 2 == 0 {
                    even_count += 1;
                }
                j += 1;
            }
            b.push(even_count);
            i += 1;
        }
        len
    }

    // Main evens method - simplified version
    fn evens(a: Vec<i32>) -> Vec<Vec<i32>> {
        let mut result = Vec::new();
        let mut current_evens = Vec::new();
        
        let mut i = 0;
        while i < a.len() {
            if a[i] % 2 == 0 {
                current_evens.push(a[i]);
            }
            i += 1;
        }
        
        result.push(current_evens);
        result
    }

    // Multiplication method
    fn mult(x: i32, y: i32) -> (r: i32) {
        x * y
    }
}

fn main() {}