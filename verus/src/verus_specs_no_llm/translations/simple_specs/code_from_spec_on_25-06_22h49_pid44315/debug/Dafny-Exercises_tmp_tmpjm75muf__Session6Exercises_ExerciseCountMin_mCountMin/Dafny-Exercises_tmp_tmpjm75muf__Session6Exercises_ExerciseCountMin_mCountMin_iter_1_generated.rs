use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function to find minimum value in a vector
spec fn min(v: Vec<int>, n: int) -> int
    decreases n
{
    if n <= 0 {
        int::MAX
    } else if n == 1 {
        v[0]
    } else {
        let rest_min = min(v, n-1);
        if v[(n-1) as nat] < rest_min { v[(n-1) as nat] } else { rest_min }
    }
}

// Spec function to count occurrences of a value in first n elements
spec fn countMin(v: Vec<int>, val: int, n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        let rest_count = countMin(v, val, n-1);
        if v[(n-1) as nat] == val { rest_count + 1 } else { rest_count }
    }
}

// Lemma: minimum of vector with n elements is same as minimum with n-1 elements
// when the nth element is greater than or equal to the minimum of first n-1 elements
proof fn lemma_min_extend(v: Vec<int>, n: int)
    requires
        0 < n < v.len(),
        v[(n-1) as nat] >= min(v, n-1)
    ensures
        min(v, n) == min(v, n-1)
    decreases n
{
    if n == 1 {
        // Base case is trivial
    } else {
        lemma_min_extend(v, n-1);
    }
}

// Lemma: if we're counting a value that's not the minimum of the first k elements,
// then the count remains the same when we extend to k elements
proof fn lemma_count_not_min(v: Vec<int>, val: int, k: int)
    requires
        0 < k <= v.len(),
        val != min(v, k),
        val != v[(k-1) as nat]
    ensures
        countMin(v, val, k) == countMin(v, val, k-1)
    decreases k
{
    // This follows directly from the definition
}

fn mCountMin(v: Vec<int>) -> (c: int)
    requires
        v.len() > 0
    ensures
        c == countMin(v, min(v, v.len() as int), v.len() as int)
{
    let mut current_min = v[0];
    let mut count = 1;
    let mut i = 1;

    while i < v.len()
        invariant
            0 < i <= v.len(),
            current_min == min(v, i as int),
            count == countMin(v, current_min, i as int),
    {
        if v[i] < current_min {
            current_min = v[i];
            count = 1;
            
            // Prove that current_min is now the minimum of first i+1 elements
            assert(min(v, (i+1) as int) == current_min);
            // Prove that count is correct for the new minimum  
            assert(countMin(v, current_min, (i+1) as int) == 1);
        } else if v[i] == current_min {
            count = count + 1;
            
            // Prove minimum doesn't change
            lemma_min_extend(v, (i+1) as int);
            assert(min(v, (i+1) as int) == current_min);
            // Count increases by 1
            assert(countMin(v, current_min, (i+1) as int) == count);
        } else {
            // v[i] > current_min, so minimum and count don't change
            lemma_min_extend(v, (i+1) as int);
            assert(min(v, (i+1) as int) == current_min);
            assert(countMin(v, current_min, (i+1) as int) == count);
        }
        i = i + 1;
    }
    
    count
}

}