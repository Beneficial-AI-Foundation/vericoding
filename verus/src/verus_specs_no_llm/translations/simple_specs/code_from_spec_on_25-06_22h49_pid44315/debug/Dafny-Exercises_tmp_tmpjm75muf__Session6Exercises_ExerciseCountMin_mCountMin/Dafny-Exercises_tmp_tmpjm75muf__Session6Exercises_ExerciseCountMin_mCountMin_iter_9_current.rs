use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function to find minimum value in a vector
spec fn min(v: Vec<int>, n: int) -> int
    requires n >= 0, n <= v.len()
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
    requires n >= 0, n <= v.len()
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
        1 < n <= v.len(),
        v[(n-1) as nat] >= min(v, n-1)
    ensures
        min(v, n) == min(v, n-1)
    decreases n
{
    // The proof follows from the definition of min
}

// Lemma: when we find a new minimum, it becomes the minimum of the extended range
proof fn lemma_new_min(v: Vec<int>, i: nat)
    requires
        0 < i < v.len(),
        v[i] < min(v, i as int)
    ensures
        min(v, (i+1) as int) == v[i]
{
    // The proof follows from the definition of min
}

// Helper lemma for proving uniqueness of new minimum
proof fn lemma_all_greater_than_new_min(v: Vec<int>, val: int, k: int)
    requires
        0 < k <= v.len(),
        val < min(v, k)
    ensures
        forall|j: int| 0 <= j < k ==> v[j as nat] > val
    decreases k
{
    if k == 1 {
        // Base case
    } else {
        let prev_min = min(v, k-1);
        if v[(k-1) as nat] < prev_min {
            lemma_all_greater_than_new_min(v, val, k-1);
        } else {
            lemma_all_greater_than_new_min(v, val, k-1);
        }
    }
}

// Lemma: when we find a new minimum, its count in the extended range is 1
proof fn lemma_new_min_count(v: Vec<int>, i: nat)
    requires
        0 < i < v.len(),
        v[i] < min(v, i as int)
    ensures
        countMin(v, v[i], (i+1) as int) == 1
{
    lemma_all_greater_than_new_min(v, v[i], i as int);
    lemma_count_zero_for_absent_value(v, v[i], i as int);
}

// Helper lemma: if a value doesn't appear in first k elements, its count is 0
proof fn lemma_count_zero_for_absent_value(v: Vec<int>, val: int, k: int)
    requires
        k <= v.len(),
        k >= 0,
        forall|j: int| 0 <= j < k ==> v[j as nat] != val
    ensures
        countMin(v, val, k) == 0
    decreases k
{
    if k <= 0 {
        // Base case: empty range has count 0
    } else {
        lemma_count_zero_for_absent_value(v, val, k-1);
    }
}

// Lemma: count increases by 1 when we encounter the same minimum
proof fn lemma_same_min_count(v: Vec<int>, val: int, i: nat)
    requires
        0 < i < v.len(),
        val == min(v, i as int),
        v[i] == val
    ensures
        countMin(v, val, (i+1) as int) == countMin(v, val, i as int) + 1
{
    // Follows directly from definition of countMin
}

// Helper lemma: count remains same when element is not equal to target
proof fn lemma_count_unchanged(v: Vec<int>, val: int, i: nat)
    requires
        0 < i < v.len(),
        v[i] != val
    ensures
        countMin(v, val, (i+1) as int) == countMin(v, val, i as int)
{
    // Follows directly from definition of countMin
}

fn mCountMin(v: Vec<int>) -> (c: int)
    requires
        v.len() > 0
    ensures
        c == countMin(v, min(v, v.len() as int), v.len() as int)
{
    let mut current_min = v[0];
    let mut count = 1;
    let mut i: usize = 1;

    while i < v.len()
        invariant
            0 < i <= v.len(),
            current_min == min(v, i as int),
            count == countMin(v, current_min, i as int),
            count >= 1,
    {
        if v[i] < current_min {
            // New minimum found
            proof {
                lemma_new_min(v, i);
                lemma_new_min_count(v, i);
            }
            
            current_min = v[i];
            count = 1;
        } else if v[i] == current_min {
            // Same minimum, increment count
            proof {
                lemma_min_extend(v, (i+1) as int);
                lemma_same_min_count(v, current_min, i);
            }
            
            count = count + 1;
        } else {
            // Element is greater than current minimum
            proof {
                lemma_min_extend(v, (i+1) as int);
                lemma_count_unchanged(v, current_min, i);
            }
        }
        i = i + 1;
    }
    
    count
}

}