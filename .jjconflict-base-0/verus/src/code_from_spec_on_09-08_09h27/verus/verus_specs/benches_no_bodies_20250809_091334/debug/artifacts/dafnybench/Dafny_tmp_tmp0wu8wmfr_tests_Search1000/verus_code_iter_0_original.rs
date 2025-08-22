use vstd::prelude::*;

verus! {
    // Author: Snorri Agnarsson, snorri@hi.is
    
    // Search1000 is a Verus version of a function shown
    // by Jon Bentley in his old Programming Pearls
    // column in CACM.  Surprisingly Verus needs no help
    // to verify the function.
    fn search1000(a: &[int], x: int) -> (k: usize)
        requires 
            a.len() >= 1000,
            forall|p: int, q: int| 0 <= p < q < 1000 ==> a[p] <= a[q],
        ensures 
            0 <= k <= 1000,
            forall|r: int| 0 <= r < k ==> a[r] < x,
            forall|r: int| k <= r < 1000 ==> a[r] >= x,
    {
    return 0;  // TODO: Remove this line and implement the function body
    }
    
    // Is2Pow(n) is true iff n==2^k for some k>=0.
    spec fn is_2_pow(n: int) -> bool
        decreases n
    {
        if n < 1 {
            false
        } else if n == 1 {
            true
        } else {
            n % 2 == 0 && is_2_pow(n / 2)
        }
    }
    
    // This method is a binary search that only works for array
    // segments of size n == 2^k-1 for some k>=0.
    fn search_2_pow_loop(a: &[int], i: usize, n: usize, x: int) -> (k: usize)
        requires 
            0 <= i && i + n <= a.len(),
            forall|p: int, q: int| i <= p < q < i + n ==> a[p] <= a[q],
            is_2_pow((n + 1) as int),
        ensures 
            i <= k && k <= i + n,
            forall|r: int| i <= r < k ==> a[r] < x,
            forall|r: int| k <= r < i + n ==> a[r] >= x,
    {
    return 0;  // TODO: Remove this line and implement the function body
    }
    
    // This method is a binary search that only works for array
    // segments of size n == 2^k-1 for some k>=0.
    fn search_2_pow_recursive(a: &[int], i: usize, n: usize, x: int) -> (k: usize)
        requires 
            0 <= i && i + n <= a.len(),
            forall|p: int, q: int| i <= p < q < i + n ==> a[p] <= a[q],
            is_2_pow((n + 1) as int),
        ensures 
            i <= k && k <= i + n,
            forall|r: int| i <= r < k ==> a[r] < x,
            forall|r: int| k <= r < i + n ==> a[r] >= x,
        decreases n
    {
    return 0;  // TODO: Remove this line and implement the function body
    }
}

fn main() {}