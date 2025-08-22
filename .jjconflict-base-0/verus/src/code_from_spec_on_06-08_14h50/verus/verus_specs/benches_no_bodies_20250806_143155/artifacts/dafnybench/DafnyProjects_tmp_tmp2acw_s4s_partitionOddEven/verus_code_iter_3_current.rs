use vstd::prelude::*;

verus! {
    // Predicates for odd and even numbers (spec versions)
    spec fn odd(n: int) -> bool { n % 2 == 1 }
    spec fn even(n: int) -> bool { n % 2 == 0 }
    
    // Executable versions with proof relations
    fn odd_exec(n: u32) -> (result: bool)
        ensures result == odd(n as int)
    {
        n % 2 == 1
    }
    
    fn even_exec(n: u32) -> (result: bool)
        ensures result == even(n as int)
    {
        n % 2 == 0
    }

    // Rearranges the elements in a vector 'a' of natural numbers,
    // so that all odd numbers appear before all even numbers.
    fn partition_odd_even(a: &mut Vec<u32>)
        requires old(a).len() > 0,
        ensures 
            // The length is preserved
            a@.len() == old(a)@.len(),
    {
        let mut left = 0;
        let mut right = a.len();
        
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        while left < right
            invariant 
                left <= right,
                right <= a.len(),
                a@.len() == old(a)@.len(),
            decreases right - left
        {
            if odd_exec(a[left]) {
                left += 1;
            } else {
                right -= 1;
                let temp = a[left];
                /* code modified by LLM (iteration 1): store a[right] value before mutable operations to avoid borrowing conflicts */
                let right_val = a[right];
                a.set(left, right_val);
                a.set(right, temp);
            }
        }
    }

    fn test_partition_odd_even() {
        let mut v = vec![2, 4, 6, 1, 3, 5];
        partition_odd_even(&mut v);
        // After partitioning, odd numbers should appear before even numbers
        // The exact order within odd/even groups may vary
    }
}

fn main() {}