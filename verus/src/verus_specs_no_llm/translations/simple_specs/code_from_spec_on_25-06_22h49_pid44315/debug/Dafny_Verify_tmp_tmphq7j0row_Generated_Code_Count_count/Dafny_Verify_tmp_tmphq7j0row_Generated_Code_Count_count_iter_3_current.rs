use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function to define what it means to count occurrences
spec fn has_count(v: int, a: Vec<int>, n: int) -> int 
    requires n >= 0
    decreases n
{
    if n <= 0 {
        0
    } else {
        has_count(v, a, n - 1) + if a[(n - 1) as nat] == v { 1 } else { 0 }
    }
}

fn count(v: int, a: Vec<int>, n: int) -> (r: int)
    requires
        n >= 0 && n <= a.len()
    ensures
        has_count(v, a, n) == r
{
    let mut count = 0;
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            count == has_count(v, a, i),
            n <= a.len(),
            i >= 0
    {
        assert(i < n);
        assert(i as nat < a.len());
        if a[i as nat] == v {
            count = count + 1;
        }
        i = i + 1;
        
        // Proof that has_count is incremental
        assert(has_count(v, a, i) == has_count(v, a, i - 1) + if a[(i - 1) as nat] == v { 1 } else { 0 });
    }
    
    count
}

}